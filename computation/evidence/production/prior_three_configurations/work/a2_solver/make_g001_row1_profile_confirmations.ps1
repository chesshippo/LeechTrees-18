$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
$runDir = Join-Path $solverDir 'row1_profile_runs'
$plan = Join-Path $rootDir `
    'outputs\G001_ROW1_PARTITION_PLAN_PROVISIONAL.csv'
$fanout = Join-Path $rootDir `
    'outputs\G001_ROW1_PARTITION_FANOUT_PROVISIONAL.csv'
$coverageVerifier = Join-Path $solverDir `
    'verify_g001_row1_partition_coverage.ps1'
$evidenceVerifier = Join-Path $solverDir `
    'verify_g001_row1_profile_evidence.ps1'

$planSha = '3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316'
$fanoutSha = 'BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E'
$coverageVerifierSha = `
    '210BBF33D4E49B14365DFDE91E4DF23B31A1AE4F7BF093C292D4E2BED8AF1AC6'
$evidenceVerifierSha = `
    '91296DDB7635C8D1683BE4F48B7976638FDDCC0D3BBD1E580040F2EF3969963F'
$planVersion = 'G001-ROW1-COVER-v3-PROVISIONAL-20260816'
$artifactSuffixes = @(
    'baseline.done.txt','baseline.stderr.txt','baseline.stdout.txt',
    'cover.done.txt','cover.stderr.txt','cover.stdout.txt','lock.txt',
    'profile.csv','profile.log'
)

function Assert-Hash {
    param([string]$Path,[string]$Expected,[string]$Label)
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing ${Label}: $Path"
    }
    $actual=(Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash
    if ($actual -cne $Expected) {
        throw "$Label hash is $actual, expected $Expected."
    }
}

function Write-AtomicLines {
    param([string]$Path,[string[]]$Lines)
    $tmp=$Path+'.tmp'
    foreach ($target in @($Path,$tmp)) {
        if (Test-Path -LiteralPath $target) {
            throw "Refusing to overwrite confirmation artifact: $target"
        }
    }
    Set-Content -LiteralPath $tmp -Value $Lines
    Move-Item -LiteralPath $tmp -Destination $Path
}

function New-ProfileConfirmation {
    param(
        [string]$ProfileSet,
        [string]$StemBase,
        [string]$BranchBase,
        [string]$ParentSelector,
        [int]$ChildCount,
        [int64]$ExpectedBaseline,
        [int64]$ExpectedCover,
        [string]$HelperRelative,
        [string]$HelperSha,
        [string]$EvidencePlanSha,
        [string]$EvidenceFanoutSha,
        [string]$ManifestRelative,
        [string]$ConfirmationRelative
    )
    $helper=Join-Path $rootDir ($HelperRelative -replace '/','\')
    Assert-Hash $helper $HelperSha "$ProfileSet helper"
    $expectedRelative=@()
    $baseline=[int64]0
    $cover=[int64]0
    for ($child=0; $child -lt $ChildCount; ++$child) {
        $stem="$ProfileSet.$StemBase`_$($child.ToString('00'))"
        foreach ($suffix in $artifactSuffixes) {
            $expectedRelative += `
                "work/a2_solver/row1_profile_runs/$stem.$suffix"
        }
        $csv=Join-Path $runDir "$stem.profile.csv"
        if (-not (Test-Path -LiteralPath $csv -PathType Leaf)) {
            throw "$ProfileSet child $child lacks its profile CSV."
        }
        $rows=@(Import-Csv -LiteralPath $csv)
        if ($rows.Count -ne 2 -or
            $rows[0].configuration -cne 'baseline' -or
            $rows[1].configuration -cne 'cover') {
            throw "$ProfileSet child $child lacks one baseline/cover pair."
        }
        for ($index=0; $index -lt 2; ++$index) {
            $configuration=@('baseline','cover')[$index]
            $row=$rows[$index]
            if ($row.profile_set -cne $ProfileSet -or
                $row.child -cne [string]$child -or
                $row.branch_path -cne "$BranchBase,$child" -or
                $row.configuration -cne $configuration -or
                $row.status -cne 'FRONTIER' -or $row.exit_code -cne '0' -or
                $row.solution_topologies -cne '0' -or
                $row.plan_sha256 -cne $EvidencePlanSha -or
                $row.fanout_sha256 -cne $EvidenceFanoutSha -or
                $row.frontier -notmatch '^(?:0|[1-9][0-9]*)$') {
                throw "$ProfileSet child $child $configuration CSV is invalid."
            }
            if ($configuration -eq 'baseline') {
                $baseline += [int64]$row.frontier
            } else {
                $cover += [int64]$row.frontier
            }
        }
    }
    $actualRelative=@(Get-ChildItem -LiteralPath $runDir -File |
        Where-Object { $_.Name -like "$ProfileSet.*" } |
        ForEach-Object { 'work/a2_solver/row1_profile_runs/'+$_.Name })
    $missing=@($expectedRelative | Where-Object { $_ -notin $actualRelative })
    $unexpected=@($actualRelative | Where-Object { $_ -notin $expectedRelative })
    if ($missing.Count -or $unexpected.Count -or
        $actualRelative.Count -ne 9*$ChildCount) {
        throw "$ProfileSet evidence set is incomplete or has extra files."
    }
    if ($baseline -ne $ExpectedBaseline -or $cover -ne $ExpectedCover) {
        throw "$ProfileSet aggregate mismatch: baseline=$baseline cover=$cover."
    }

    $manifestPath=Join-Path $rootDir ($ManifestRelative -replace '/','\')
    $manifestLines=@()
    foreach ($relative in $expectedRelative) {
        $full=Join-Path $rootDir ($relative -replace '/','\')
        $hash=(Get-FileHash -LiteralPath $full -Algorithm SHA256).Hash
        $manifestLines += "$hash  $relative"
    }
    Write-AtomicLines $manifestPath $manifestLines
    $manifestSha=(Get-FileHash -LiteralPath $manifestPath `
        -Algorithm SHA256).Hash
    $confirmationPath=Join-Path $rootDir `
        ($ConfirmationRelative -replace '/','\')
    $confirmed=[DateTimeOffset]::Now.ToString('o')
    $confirmationLines=@(
        'status=CONFIRMED',
        "plan_version=$planVersion",
        "plan_sha256=$planSha",
        "fanout_sha256=$fanoutSha",
        "coverage_verifier_sha256=$coverageVerifierSha",
        "evidence_verifier_sha256=$evidenceVerifierSha",
        "profile_set=$ProfileSet",
        "parent_selector=$ParentSelector",
        "child_count=$ChildCount",
        "parent_baseline_frontier=$ExpectedBaseline",
        "parent_cover_frontier=$ExpectedCover",
        "children_baseline_frontier_sum=$baseline",
        "children_cover_frontier_sum=$cover",
        "profile_helper_path=$HelperRelative",
        "profile_helper_sha256=$HelperSha",
        "evidence_plan_sha256=$EvidencePlanSha",
        "evidence_fanout_sha256=$EvidenceFanoutSha",
        "evidence_manifest_path=$ManifestRelative",
        "evidence_manifest_sha256=$manifestSha",
        "evidence_artifact_count=$($expectedRelative.Count)",
        "confirmed_local=$confirmed"
    )
    Write-AtomicLines $confirmationPath $confirmationLines
    Write-Output "CREATED profile_set=$ProfileSet children=$ChildCount baseline=$baseline cover=$cover artifacts=$($expectedRelative.Count)"
    Write-Output "manifest=$manifestPath sha256=$manifestSha"
    Write-Output "confirmation=$confirmationPath"
}

Assert-Hash $plan $planSha 'v3 plan'
Assert-Hash $fanout $fanoutSha 'v3 fan-out certificate'
Assert-Hash $coverageVerifier $coverageVerifierSha 'coverage verifier'
Assert-Hash $evidenceVerifier $evidenceVerifierSha 'evidence verifier'

New-ProfileConfirmation `
    'row1_split49_v1' 'path_2_9_15' '2,9,15' 'path:2,9,15' `
    23 1552327 689509 `
    'work/a2_solver/profile_g001_row1_path_2_9_15_children.ps1' `
    'DD19E69CDCDEE33D024BFFBD05172D5447941223B2881C20FB7859BCED2297B1' `
    '7603A7D44363A8F4D299D0742AC09C44BF01CB2F63940508EE9C1402B8147750' `
    'D1B3B8EDCEDD8ABB248E3C34F5FF979BE1183FCE502B4B3C7CB937DA08C1D78B' `
    'outputs/G001_ROW1_PATH_2_9_15_PROFILE_EVIDENCE_SHA256.txt' `
    'outputs/G001_ROW1_PATH_2_9_15_PROFILE_CONFIRMATION.txt'

New-ProfileConfirmation `
    'row1_split79_v1' 'path_2_9_15_22' '2,9,15,22' `
    'path:2,9,15,22' 31 489707 277927 `
    'work/a2_solver/profile_g001_row1_path_2_9_15_22_children.ps1' `
    'A6DE937CA411CCCB711B7E4821F47987C393F8F13271394773BC48401DE92135' `
    '3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316' `
    'BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E' `
    'outputs/G001_ROW1_PATH_2_9_15_22_PROFILE_EVIDENCE_SHA256.txt' `
    'outputs/G001_ROW1_PATH_2_9_15_22_PROFILE_CONFIRMATION.txt'

Write-Output 'G001_ROW1_PROFILE_CONFIRMATIONS_CREATED'
