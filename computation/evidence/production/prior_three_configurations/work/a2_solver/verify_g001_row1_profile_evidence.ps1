param(
    [string] $Layer23Confirmation = '',
    [string] $Layer31Confirmation = ''
)

$ErrorActionPreference = 'Stop'
$selfPath = $MyInvocation.MyCommand.Path
$solverDir = Split-Path -Parent $selfPath
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
$runDir = Join-Path $solverDir 'row1_profile_runs'
$coverageVerifier = Join-Path $solverDir `
    'verify_g001_row1_partition_coverage.ps1'
$plan = Join-Path $rootDir `
    'outputs\G001_ROW1_PARTITION_PLAN_PROVISIONAL.csv'
$fanout = Join-Path $rootDir `
    'outputs\G001_ROW1_PARTITION_FANOUT_PROVISIONAL.csv'
if (-not $Layer23Confirmation) {
    $Layer23Confirmation = Join-Path $rootDir `
        'outputs\G001_ROW1_PATH_2_9_15_PROFILE_CONFIRMATION.txt'
}
if (-not $Layer31Confirmation) {
    $Layer31Confirmation = Join-Path $rootDir `
        'outputs\G001_ROW1_PATH_2_9_15_22_PROFILE_CONFIRMATION.txt'
}

$expectedSolverSha256 = `
    '5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD'
$expectedSourceSha256 = `
    '134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9'
$expectedPlanSha256 = `
    '3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316'
$expectedFanoutSha256 = `
    'BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E'
$expectedPlanVersion = 'G001-ROW1-COVER-v3-PROVISIONAL-20260816'
$productionFlags = @(
    '--multi-edge-cover','--multi-edge-cover-no-hall',
    '--multi-edge-cover-max-components','6',
    '--multi-edge-cover-budget','100',
    '--multi-edge-cover-no-exact-hall'
)
$profileColumns = @(
    'profile_set','child','branch_path','configuration','status','exit_code',
    'wall_seconds','nodes','frontier','solution_topologies','multi_cover',
    'cover_validation_fail','solver_sha256','source_sha256','plan_sha256',
    'fanout_sha256','arguments','result_line','stdout_path','stderr_path',
    'done_path','started_local','ended_local'
)
$confirmationKeys = @(
    'status','plan_version','plan_sha256','fanout_sha256',
    'coverage_verifier_sha256','evidence_verifier_sha256','profile_set',
    'parent_selector','child_count','parent_baseline_frontier',
    'parent_cover_frontier','children_baseline_frontier_sum',
    'children_cover_frontier_sum','profile_helper_path',
    'profile_helper_sha256','evidence_plan_sha256',
    'evidence_fanout_sha256','evidence_manifest_path',
    'evidence_manifest_sha256','evidence_artifact_count','confirmed_local'
)
$artifactSuffixes = @(
    'baseline.done.txt','baseline.stderr.txt','baseline.stdout.txt',
    'cover.done.txt','cover.stderr.txt','cover.stdout.txt','lock.txt',
    'profile.csv','profile.log'
)

function Assert-ExactOrderedStrings {
    param([object[]]$Actual,[object[]]$Expected,[string]$Label)
    if ($Actual.Count -ne $Expected.Count) {
        throw "$Label count is $($Actual.Count), expected $($Expected.Count)."
    }
    for ($i=0; $i -lt $Expected.Count; ++$i) {
        if ([string]$Actual[$i] -cne [string]$Expected[$i]) {
            throw "$Label item $i is '$($Actual[$i])', expected '$($Expected[$i])'."
        }
    }
}

function Assert-ExactSet {
    param([object[]]$Actual,[object[]]$Expected,[string]$Label)
    $duplicate = @($Actual | Group-Object | Where-Object Count -ne 1)
    $missing = @($Expected | Where-Object { $_ -notin $Actual })
    $unexpected = @($Actual | Where-Object { $_ -notin $Expected })
    if ($duplicate.Count -or $missing.Count -or $unexpected.Count -or
        $Actual.Count -ne $Expected.Count) {
        throw "$Label mismatch; duplicates=[$($duplicate.Name -join ',')] missing=[$($missing -join ',')] unexpected=[$($unexpected -join ',')]."
    }
}

function Read-StrictKeyValueFile {
    param([string]$Path,[string[]]$ExpectedKeys,[string]$Label)
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing $Label artifact: $Path"
    }
    $lines = @(Get-Content -LiteralPath $Path)
    if ($lines.Count -ne $ExpectedKeys.Count) {
        throw "$Label has $($lines.Count) lines, expected $($ExpectedKeys.Count)."
    }
    $values = [ordered]@{}
    for ($i=0; $i -lt $lines.Count; ++$i) {
        if ($lines[$i] -notmatch '^([A-Za-z0-9_]+)=(.*)$') {
            throw "Malformed $Label line $($i+1): $($lines[$i])"
        }
        $key=$matches[1]
        if ($key -cne $ExpectedKeys[$i] -or $values.Contains($key)) {
            throw "$Label key $i is invalid or duplicated: $key"
        }
        $values[$key]=$matches[2]
    }
    return $values
}

function Get-ResultValues {
    param([string]$Line)
    $tokens=@($Line.Split(@(' '),[StringSplitOptions]::RemoveEmptyEntries))
    if ($tokens.Count -lt 2 -or $tokens[0] -cne 'RESULT') {
        throw "Malformed RESULT line: $Line"
    }
    $values=[ordered]@{}
    for ($i=1; $i -lt $tokens.Count; ++$i) {
        $separator=$tokens[$i].IndexOf('=')
        if ($separator -le 0) { throw "Malformed RESULT token: $($tokens[$i])" }
        $key=$tokens[$i].Substring(0,$separator)
        $value=$tokens[$i].Substring($separator+1)
        if ($key -notmatch '^[A-Za-z0-9_]+$' -or $values.Contains($key)) {
            throw "Invalid or duplicate RESULT key: $key"
        }
        $values[$key]=$value
    }
    return $values
}

function ConvertTo-StrictNonnegativeInt64 {
    param([string]$Text,[string]$Label,[switch]$Positive)
    if ($Text -notmatch '^(?:0|[1-9][0-9]*)$') {
        throw "$Label is not a canonical nonnegative integer: '$Text'."
    }
    try { $value=[int64]::Parse($Text) }
    catch { throw "$Label is outside Int64 range: '$Text'." }
    if ($Positive -and $value -le 0) { throw "$Label must be positive." }
    return $value
}

function ConvertTo-RoundTripTimestamp {
    param([string]$Text,[string]$Label)
    try {
        return [DateTimeOffset]::Parse(
            $Text,[Globalization.CultureInfo]::InvariantCulture,
            [Globalization.DateTimeStyles]::RoundtripKind)
    } catch { throw "$Label is not a round-trip timestamp: '$Text'." }
}

function Resolve-WorkspaceRelativeFile {
    param([string]$Relative,[string]$Label)
    if ([IO.Path]::IsPathRooted($Relative) -or
        $Relative -notmatch '^(?:work|outputs)/[A-Za-z0-9_./-]+$') {
        throw "$Label is not a canonical workspace-relative path: $Relative"
    }
    $full=[IO.Path]::GetFullPath((Join-Path $rootDir ($Relative -replace '/','\')))
    $prefix=$rootDir.TrimEnd('\')+'\'
    if (-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or
        -not (Test-Path -LiteralPath $full -PathType Leaf)) {
        throw "$Label does not resolve to a workspace file: $Relative"
    }
    return $full
}

function Get-ExpectedArtifactPaths {
    param([string]$ProfileSet,[string]$StemBase,[int]$ChildCount)
    $paths=@()
    for ($child=0; $child -lt $ChildCount; ++$child) {
        $stem="$ProfileSet.$StemBase`_$($child.ToString('00'))"
        foreach ($suffix in $artifactSuffixes) {
            $paths += "work/a2_solver/row1_profile_runs/$stem.$suffix"
        }
    }
    return $paths
}

function Assert-ProfileEvidence {
    param(
        [string]$ConfirmationPath,
        [string]$Label,
        [string]$ProfileSet,
        [string]$StemBase,
        [string]$BranchBase,
        [string]$ParentSelector,
        [int]$ChildCount,
        [int64]$ExpectedBaselineFrontier,
        [int64]$ExpectedCoverFrontier,
        [string]$ExpectedHelperRelative,
        [string]$ExpectedHelperSha256,
        [string]$EvidencePlanSha256,
        [string]$EvidenceFanoutSha256,
        [string]$ExpectedManifestRelative
    )
    $confirmation=Read-StrictKeyValueFile `
        $ConfirmationPath $confirmationKeys "$Label confirmation"
    $currentCoverageVerifierSha=(Get-FileHash -LiteralPath $coverageVerifier `
        -Algorithm SHA256).Hash
    $currentEvidenceVerifierSha=(Get-FileHash -LiteralPath $selfPath `
        -Algorithm SHA256).Hash
    if ($confirmation.status -cne 'CONFIRMED' -or
        $confirmation.plan_version -cne $expectedPlanVersion -or
        $confirmation.plan_sha256 -cne $expectedPlanSha256 -or
        $confirmation.fanout_sha256 -cne $expectedFanoutSha256 -or
        $confirmation.coverage_verifier_sha256 -cne $currentCoverageVerifierSha -or
        $confirmation.evidence_verifier_sha256 -cne $currentEvidenceVerifierSha -or
        $confirmation.profile_set -cne $ProfileSet -or
        $confirmation.parent_selector -cne $ParentSelector -or
        $confirmation.child_count -cne [string]$ChildCount -or
        $confirmation.parent_baseline_frontier -cne [string]$ExpectedBaselineFrontier -or
        $confirmation.parent_cover_frontier -cne [string]$ExpectedCoverFrontier -or
        $confirmation.children_baseline_frontier_sum -cne [string]$ExpectedBaselineFrontier -or
        $confirmation.children_cover_frontier_sum -cne [string]$ExpectedCoverFrontier -or
        $confirmation.profile_helper_path -cne $ExpectedHelperRelative -or
        $confirmation.profile_helper_sha256 -cne $ExpectedHelperSha256 -or
        $confirmation.evidence_plan_sha256 -cne $EvidencePlanSha256 -or
        $confirmation.evidence_fanout_sha256 -cne $EvidenceFanoutSha256 -or
        $confirmation.evidence_manifest_path -cne $ExpectedManifestRelative -or
        $confirmation.evidence_artifact_count -cne [string](9*$ChildCount)) {
        throw "$Label confirmation metadata is not exactly frozen."
    }
    ConvertTo-RoundTripTimestamp $confirmation.confirmed_local `
        "$Label confirmation time" | Out-Null
    $helper=Resolve-WorkspaceRelativeFile `
        $confirmation.profile_helper_path "$Label helper"
    if ((Get-FileHash -LiteralPath $helper -Algorithm SHA256).Hash -cne
        $ExpectedHelperSha256) { throw "$Label helper hash mismatch." }
    $manifest=Resolve-WorkspaceRelativeFile `
        $confirmation.evidence_manifest_path "$Label manifest"
    $manifestSha=(Get-FileHash -LiteralPath $manifest -Algorithm SHA256).Hash
    if ($manifestSha -cne $confirmation.evidence_manifest_sha256) {
        throw "$Label manifest hash mismatch."
    }

    $expectedPaths=@(Get-ExpectedArtifactPaths `
        $ProfileSet $StemBase $ChildCount)
    $manifestLines=@(Get-Content -LiteralPath $manifest)
    if ($manifestLines.Count -ne $expectedPaths.Count) {
        throw "$Label manifest has $($manifestLines.Count) entries, expected $($expectedPaths.Count)."
    }
    $manifestPaths=@()
    for ($i=0; $i -lt $manifestLines.Count; ++$i) {
        if ($manifestLines[$i] -notmatch '^([A-F0-9]{64})  (.+)$') {
            throw "$Label manifest line $($i+1) is malformed."
        }
        $recordedHash=$matches[1]
        $relative=$matches[2]
        if ($relative -cne $expectedPaths[$i]) {
            throw "$Label manifest path $i is '$relative', expected '$($expectedPaths[$i])'."
        }
        $full=Resolve-WorkspaceRelativeFile $relative "$Label evidence"
        $actualHash=(Get-FileHash -LiteralPath $full -Algorithm SHA256).Hash
        if ($actualHash -cne $recordedHash) {
            throw "$Label evidence hash mismatch: $relative"
        }
        $manifestPaths += $relative
    }
    Assert-ExactSet $manifestPaths $expectedPaths "$Label manifest paths"
    $actualProfileFiles=@(Get-ChildItem -LiteralPath $runDir -File |
        Where-Object { $_.Name -like "$ProfileSet.*" } |
        ForEach-Object { 'work/a2_solver/row1_profile_runs/'+$_.Name })
    Assert-ExactSet $actualProfileFiles $expectedPaths `
        "$Label profile-set artifacts"

    $baselineSum=[int64]0
    $coverSum=[int64]0
    for ($child=0; $child -lt $ChildCount; ++$child) {
        $stem="$ProfileSet.$StemBase`_$($child.ToString('00'))"
        $csvRelative="work/a2_solver/row1_profile_runs/$stem.profile.csv"
        $csv=Resolve-WorkspaceRelativeFile $csvRelative "$Label child $child CSV"
        $rows=@(Import-Csv -LiteralPath $csv)
        if ($rows.Count -ne 2) { throw "$Label child $child CSV must have two rows." }
        Assert-ExactOrderedStrings @($rows[0].PSObject.Properties.Name) `
            $profileColumns "$Label child $child CSV columns"
        $lock=Resolve-WorkspaceRelativeFile `
            "work/a2_solver/row1_profile_runs/$stem.lock.txt" `
            "$Label child $child lock"
        $lockLines=@(Get-Content -LiteralPath $lock)
        if ($lockLines.Count -ne 4 -or
            $lockLines[0] -cne "profile_set=$ProfileSet" -or
            $lockLines[1] -cne "child=$child" -or
            $lockLines[2] -notmatch '^claimed_local=.+$' -or
            $lockLines[3] -notmatch '^completed_local=.+$') {
            throw "$Label child $child lock is not complete."
        }
        $log=Resolve-WorkspaceRelativeFile `
            "work/a2_solver/row1_profile_runs/$stem.profile.log" `
            "$Label child $child log"
        $logLines=@(Get-Content -LiteralPath $log)
        if ($logLines.Count -ne 15 -or
            $logLines[0] -cne "PROFILE_SET=$ProfileSet" -or
            $logLines[1] -cne "CHILD=$child" -or
            $logLines[2] -cne "BRANCH_PATH=$BranchBase,$child" -or
            $logLines[3] -cne "SOLVER_SHA256=$expectedSolverSha256" -or
            $logLines[4] -cne "SOURCE_SHA256=$expectedSourceSha256" -or
            $logLines[5] -cne "PLAN_SHA256=$EvidencePlanSha256" -or
            $logLines[6] -cne "FANOUT_SHA256=$EvidenceFanoutSha256") {
            throw "$Label child $child log header is invalid."
        }
        for ($index=0; $index -lt 2; ++$index) {
            $configuration=@('baseline','cover')[$index]
            $row=$rows[$index]
            $branchPath="$BranchBase,$child"
            $arguments=@('--mode','g001_row1','--branch-path',$branchPath,
                '--stop-edges','12')
            if ($configuration -eq 'cover') { $arguments += $productionFlags }
            $argumentLine=$arguments -join ' '
            if ($row.profile_set -cne $ProfileSet -or
                $row.child -cne [string]$child -or
                $row.branch_path -cne $branchPath -or
                $row.configuration -cne $configuration -or
                $row.status -cne 'FRONTIER' -or $row.exit_code -cne '0' -or
                $row.solution_topologies -cne '0' -or
                $row.solver_sha256 -cne $expectedSolverSha256 -or
                $row.source_sha256 -cne $expectedSourceSha256 -or
                $row.plan_sha256 -cne $EvidencePlanSha256 -or
                $row.fanout_sha256 -cne $EvidenceFanoutSha256 -or
                $row.arguments -cne $argumentLine) {
                throw "$Label child $child $configuration CSV binding failed."
            }
            $result=Get-ResultValues $row.result_line
            foreach ($required in @(
                'mode','status','nodes','states','generated','frontier',
                'solution_topologies','root_valid','cutlower','cutupper',
                'late_t9a')) {
                if (-not $result.Contains($required)) {
                    throw "$Label child $child $configuration RESULT lacks $required."
                }
            }
            if ($result.mode -cne 'g001_row1' -or
                $result.status -cne 'FRONTIER' -or
                $result.solution_topologies -cne '0' -or
                $result.root_valid -cne '3' -or
                $result.cutlower -cne '0' -or $result.cutupper -cne '0' -or
                $result.late_t9a -cne '0' -or
                $row.nodes -cne $result.nodes -or
                $row.frontier -cne $result.frontier) {
                throw "$Label child $child $configuration RESULT invariants failed."
            }
            ConvertTo-StrictNonnegativeInt64 $result.nodes `
                "$Label child $child $configuration nodes" -Positive|Out-Null
            $frontier=ConvertTo-StrictNonnegativeInt64 $result.frontier `
                "$Label child $child $configuration frontier"
            if ($configuration -eq 'cover') {
                if (-not $result.Contains('multi_cover') -or
                    -not $result.Contains('cover_validation_fail') -or
                    $result.multi_cover -cne 'on' -or
                    $result.cover_validation_fail -cne '0' -or
                    $row.multi_cover -cne 'on' -or
                    $row.cover_validation_fail -cne '0') {
                    throw "$Label child $child cover invariants failed."
                }
                $coverSum += $frontier
            } else {
                if ($result.Contains('multi_cover') -or
                    $row.multi_cover -cne 'off' -or
                    $row.cover_validation_fail -cne 'not_applicable') {
                    throw "$Label child $child baseline enabled cover."
                }
                $baselineSum += $frontier
            }
            $stdoutRelative="work/a2_solver/row1_profile_runs/$stem.$configuration.stdout.txt"
            $stderrRelative="work/a2_solver/row1_profile_runs/$stem.$configuration.stderr.txt"
            $doneRelative="work/a2_solver/row1_profile_runs/$stem.$configuration.done.txt"
            if ($row.stdout_path -cne $stdoutRelative -or
                $row.stderr_path -cne $stderrRelative -or
                $row.done_path -cne $doneRelative) {
                throw "$Label child $child $configuration raw paths differ."
            }
            $stdout=Resolve-WorkspaceRelativeFile $stdoutRelative 'stdout'
            $stderr=Resolve-WorkspaceRelativeFile $stderrRelative 'stderr'
            $done=Resolve-WorkspaceRelativeFile $doneRelative 'done'
            if ((Get-Item -LiteralPath $stderr).Length -ne 0) {
                throw "$Label child $child $configuration has nonempty stderr."
            }
            $stdoutLines=@(Get-Content -LiteralPath $stdout)
            if ($stdoutLines.Count -ne 1 -or
                $stdoutLines[0] -cne $row.result_line) {
                throw "$Label child $child $configuration stdout differs."
            }
            $doneKeys=@('exit_code','wall_seconds','started_local','ended_local',
                'solver_sha256','source_sha256','arguments')
            $doneValues=Read-StrictKeyValueFile $done $doneKeys `
                "$Label child $child $configuration done"
            if ($doneValues.exit_code -cne '0' -or
                $doneValues.wall_seconds -cne $row.wall_seconds -or
                $doneValues.started_local -cne $row.started_local -or
                $doneValues.ended_local -cne $row.ended_local -or
                $doneValues.solver_sha256 -cne $expectedSolverSha256 -or
                $doneValues.source_sha256 -cne $expectedSourceSha256 -or
                $doneValues.arguments -cne $argumentLine) {
                throw "$Label child $child $configuration done differs."
            }
            $baseIndex=if ($configuration -eq 'baseline') {7} else {11}
            if ($logLines[$baseIndex] -cne
                    "START configuration=$configuration started_local=$($row.started_local)" -or
                $logLines[$baseIndex+1] -cne "arguments=$argumentLine" -or
                $logLines[$baseIndex+2] -cne
                    "END configuration=$configuration exit_code=0 wall_seconds=$($row.wall_seconds) ended_local=$($row.ended_local)" -or
                $logLines[$baseIndex+3] -cne
                    "RESULT configuration=$configuration $($row.result_line)") {
                throw "$Label child $child $configuration log differs."
            }
        }
    }
    if ($baselineSum -ne $ExpectedBaselineFrontier -or
        $coverSum -ne $ExpectedCoverFrontier) {
        throw "$Label aggregate mismatch: baseline=$baselineSum cover=$coverSum."
    }
    Write-Output "PROFILE_EVIDENCE_OK label=$Label children=$ChildCount baseline_frontier=$baselineSum cover_frontier=$coverSum artifacts=$($expectedPaths.Count)"
}

if ((Get-FileHash -LiteralPath $plan -Algorithm SHA256).Hash -cne
    $expectedPlanSha256) { throw 'Current v3 plan hash mismatch.' }
if ((Get-FileHash -LiteralPath $fanout -Algorithm SHA256).Hash -cne
    $expectedFanoutSha256) { throw 'Current v3 fan-out hash mismatch.' }

Assert-ProfileEvidence `
    $Layer23Confirmation 'layer23' 'row1_split49_v1' 'path_2_9_15' `
    '2,9,15' 'path:2,9,15' 23 1552327 689509 `
    'work/a2_solver/profile_g001_row1_path_2_9_15_children.ps1' `
    'DD19E69CDCDEE33D024BFFBD05172D5447941223B2881C20FB7859BCED2297B1' `
    '7603A7D44363A8F4D299D0742AC09C44BF01CB2F63940508EE9C1402B8147750' `
    'D1B3B8EDCEDD8ABB248E3C34F5FF979BE1183FCE502B4B3C7CB937DA08C1D78B' `
    'outputs/G001_ROW1_PATH_2_9_15_PROFILE_EVIDENCE_SHA256.txt'

Assert-ProfileEvidence `
    $Layer31Confirmation 'layer31' 'row1_split79_v1' `
    'path_2_9_15_22' '2,9,15,22' 'path:2,9,15,22' 31 489707 277927 `
    'work/a2_solver/profile_g001_row1_path_2_9_15_22_children.ps1' `
    'A6DE937CA411CCCB711B7E4821F47987C393F8F13271394773BC48401DE92135' `
    '3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316' `
    'BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E' `
    'outputs/G001_ROW1_PATH_2_9_15_22_PROFILE_EVIDENCE_SHA256.txt'

Write-Output 'G001_ROW1_PROFILE_EVIDENCE_OK'
