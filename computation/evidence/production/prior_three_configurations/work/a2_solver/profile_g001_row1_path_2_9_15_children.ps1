param(
    [Parameter(Mandatory = $true)]
    [ValidatePattern('^[A-Za-z0-9][A-Za-z0-9_.-]*$')]
    [string] $ProfileSet,

    [ValidateRange(0,22)] [int] $FirstChild = 0,
    [ValidateRange(0,22)] [int] $LastChild = 22,
    [switch] $DryRun,
    [switch] $AggregateOnly
)

# Profiles the exact 23-way split below row-1 path 2,9,15 at depth 12.
# Examples:
#   .\profile_g001_row1_path_2_9_15_children.ps1 `
#       -ProfileSet row1_split_v2 -FirstChild 0 -LastChild 7
#   .\profile_g001_row1_path_2_9_15_children.ps1 `
#       -ProfileSet row1_split_v2 -AggregateOnly
#
# Different processes may use the same ProfileSet only when their child
# ranges are disjoint.  Every child has an atomic, permanent lock file and
# independent artifacts; no shared CSV is written during profiling.

$ErrorActionPreference = 'Stop'
if ($FirstChild -gt $LastChild) {
    throw 'FirstChild must not exceed LastChild.'
}
if ($DryRun -and $AggregateOnly) {
    throw 'Choose either DryRun or AggregateOnly, not both.'
}

$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
$runDir = Join-Path $solverDir 'row1_profile_runs'
$solver = Join-Path $solverDir 'order18_topology_free_search_row1.exe'
$source = Join-Path $solverDir `
    'order18_topology_free_search_row1_snapshot.cpp'
$exactCoverHeader = Join-Path $solverDir 'a2_multi_edge_exact_cover.hpp'
$optimizedHeader = Join-Path $solverDir `
    'a2_multi_edge_exact_cover_optimized.hpp'
$strongerHeader = Join-Path $solverDir `
    'a2_multi_edge_stronger_relaxation.hpp'
$parityHeader = Join-Path $solverDir 'multi_edge_parity_coherence.hpp'
$plan = Join-Path $rootDir `
    'outputs\G001_ROW1_PARTITION_PLAN_PROVISIONAL.csv'
$fanout = Join-Path $rootDir `
    'outputs\G001_ROW1_PARTITION_FANOUT_PROVISIONAL.csv'

$expectedSolverSha256 = `
    '5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD'
$expectedSourceSha256 = `
    '134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9'
$expectedPlanSha256 = `
    '7603A7D44363A8F4D299D0742AC09C44BF01CB2F63940508EE9C1402B8147750'
$expectedFanoutSha256 = `
    'D1B3B8EDCEDD8ABB248E3C34F5FF979BE1183FCE502B4B3C7CB937DA08C1D78B'
$expectedHashes = [ordered]@{
    $solver = $expectedSolverSha256
    $source = $expectedSourceSha256
    $exactCoverHeader = `
        'C156EAE52BCEEF28DB0DF1A38D10DEA253DE09E5F627D0952A6BB1B9356CD813'
    $optimizedHeader = `
        '5320C920E800CE2F9E2348B90D672E26CDDD748B43BC02BC24B9146DEDB5E48B'
    $strongerHeader = `
        'E58F917A631C48F2419835D41C2B0EE164F0D24F44BA489C152B9C00CDDBBD5C'
    $parityHeader = `
        'AF09E37C9E50FB3891BB11BBFEAD6D5F8299200C7ABF81BC8049FB20A07D30C7'
    $plan = $expectedPlanSha256
    $fanout = $expectedFanoutSha256
}

$productionFlags = @(
    '--multi-edge-cover',
    '--multi-edge-cover-no-hall',
    '--multi-edge-cover-max-components', '6',
    '--multi-edge-cover-budget', '100',
    '--multi-edge-cover-no-exact-hall'
)
$targetBaselineFrontier = [int64]1552327
$targetCoverFrontier = [int64]689509
$profileColumns = @(
    'profile_set','child','branch_path','configuration','status','exit_code',
    'wall_seconds','nodes','frontier','solution_topologies','multi_cover',
    'cover_validation_fail','solver_sha256','source_sha256','plan_sha256',
    'fanout_sha256','arguments','result_line','stdout_path','stderr_path',
    'done_path','started_local','ended_local'
)

function Assert-ExactOrderedStrings {
    param(
        [object[]] $Actual,
        [object[]] $Expected,
        [string] $Label
    )
    if ($Actual.Count -ne $Expected.Count) {
        throw "$Label count is $($Actual.Count), expected $($Expected.Count)."
    }
    for ($i = 0; $i -lt $Expected.Count; ++$i) {
        if ([string]$Actual[$i] -cne [string]$Expected[$i]) {
            throw "$Label item $i is '$($Actual[$i])', expected '$($Expected[$i])'."
        }
    }
}

function Read-StrictKeyValueFile {
    param(
        [string] $Path,
        [string[]] $ExpectedKeys,
        [string] $Label
    )
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing $Label artifact: $Path"
    }
    $lines = @(Get-Content -LiteralPath $Path)
    if ($lines.Count -ne $ExpectedKeys.Count) {
        throw "$Label has $($lines.Count) lines, expected $($ExpectedKeys.Count)."
    }
    $values = [ordered]@{}
    for ($i = 0; $i -lt $lines.Count; ++$i) {
        if ($lines[$i] -notmatch '^([A-Za-z0-9_]+)=(.*)$') {
            throw "Malformed $Label line $($i + 1): $($lines[$i])"
        }
        $key = $matches[1]
        if ($key -cne $ExpectedKeys[$i] -or $values.Contains($key)) {
            throw "$Label key $i is invalid or duplicated: $key"
        }
        $values[$key] = $matches[2]
    }
    return $values
}

function Get-ResultValues {
    param([string] $Line)
    $tokens = @($Line.Split(
        @(' '), [StringSplitOptions]::RemoveEmptyEntries))
    if ($tokens.Count -lt 2 -or $tokens[0] -cne 'RESULT') {
        throw "Malformed RESULT line: $Line"
    }
    $values = [ordered]@{}
    for ($i = 1; $i -lt $tokens.Count; ++$i) {
        $separator = $tokens[$i].IndexOf('=')
        if ($separator -le 0) {
            throw "Malformed RESULT token: $($tokens[$i])"
        }
        $key = $tokens[$i].Substring(0, $separator)
        $value = $tokens[$i].Substring($separator + 1)
        if ($key -notmatch '^[A-Za-z0-9_]+$' -or
            $values.Contains($key)) {
            throw "Invalid or duplicate RESULT key: $key"
        }
        $values[$key] = $value
    }
    return $values
}

function ConvertTo-StrictNonnegativeInt64 {
    param(
        [string] $Text,
        [string] $Label,
        [switch] $Positive
    )
    if ($Text -notmatch '^(?:0|[1-9][0-9]*)$') {
        throw "$Label is not a canonical nonnegative integer: '$Text'."
    }
    try { $value = [int64]::Parse($Text) }
    catch { throw "$Label is outside Int64 range: '$Text'." }
    if ($Positive -and $value -le 0) { throw "$Label must be positive." }
    return $value
}

function ConvertTo-StrictPositiveDouble {
    param(
        [string] $Text,
        [string] $Label
    )
    if ($Text -notmatch `
        '^(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[Ee][+-]?[0-9]+)?$') {
        throw "$Label is not a canonical nonnegative real: '$Text'."
    }
    try {
        $value = [double]::Parse(
            $Text, [Globalization.CultureInfo]::InvariantCulture)
    } catch { throw "$Label is not a floating-point number: '$Text'." }
    if ([double]::IsNaN($value) -or [double]::IsInfinity($value) -or
        $value -le 0) {
        throw "$Label must be positive and finite."
    }
    return $value
}

function Get-WorkspaceRelativePath {
    param([string] $Path)
    $absolute = [IO.Path]::GetFullPath($Path)
    $prefix = $rootDir.TrimEnd('\') + '\'
    if (-not $absolute.StartsWith(
        $prefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Artifact is outside the workspace: $absolute"
    }
    return $absolute.Substring($prefix.Length).Replace('\','/')
}

function Get-ChildStem {
    param([int] $Child)
    return "$ProfileSet.path_2_9_15_$($Child.ToString('00'))"
}

function Get-ChildArtifacts {
    param([int] $Child)
    $stem = Get-ChildStem $Child
    $artifacts = [ordered]@{
        stem = $stem
        lock = Join-Path $runDir "$stem.lock.txt"
        log = Join-Path $runDir "$stem.profile.log"
        csv = Join-Path $runDir "$stem.profile.csv"
    }
    foreach ($configuration in @('baseline','cover')) {
        $artifacts["${configuration}_stdout"] = `
            Join-Path $runDir "$stem.$configuration.stdout.txt"
        $artifacts["${configuration}_stderr"] = `
            Join-Path $runDir "$stem.$configuration.stderr.txt"
        $artifacts["${configuration}_done"] = `
            Join-Path $runDir "$stem.$configuration.done.txt"
        $artifacts["${configuration}_done_tmp"] = `
            Join-Path $runDir "$stem.$configuration.done.tmp"
    }
    return $artifacts
}

function Get-Arguments {
    param(
        [int] $Child,
        [string] $Configuration
    )
    $arguments = @(
        '--mode','g001_row1',
        '--branch-path',"2,9,15,$Child",
        '--stop-edges','12'
    )
    if ($Configuration -eq 'cover') { $arguments += $productionFlags }
    elseif ($Configuration -ne 'baseline') {
        throw "Unknown configuration: $Configuration"
    }
    return $arguments
}

function Assert-ProfileResult {
    param(
        [int] $Child,
        [string] $Configuration,
        [string] $ResultLine
    )
    $result = Get-ResultValues $ResultLine
    foreach ($required in @(
        'mode','status','nodes','states','generated','solution_topologies',
        'root_valid','frontier','cutlower','cutupper','late_t9a')) {
        if (-not $result.Contains($required)) {
            throw "Child $Child $Configuration RESULT lacks $required."
        }
    }
    if ($result.mode -cne 'g001_row1' -or
        $result.status -cne 'FRONTIER' -or
        $result.solution_topologies -cne '0' -or
        $result.root_valid -cne '3' -or
        $result.cutlower -cne '0' -or $result.cutupper -cne '0' -or
        $result.late_t9a -cne '0') {
        throw "Child $Child $Configuration has invalid profile invariants."
    }
    foreach ($counter in @('nodes','states','generated')) {
        ConvertTo-StrictNonnegativeInt64 $result[$counter] `
            "child $Child $Configuration $counter" -Positive | Out-Null
    }
    ConvertTo-StrictNonnegativeInt64 $result.frontier `
        "child $Child $Configuration frontier" | Out-Null
    if ($Configuration -eq 'cover') {
        foreach ($required in @('multi_cover','cover_validation_fail')) {
            if (-not $result.Contains($required)) {
                throw "Child $Child cover RESULT lacks $required."
            }
        }
        if ($result.multi_cover -cne 'on' -or
            $result.cover_validation_fail -cne '0') {
            throw "Child $Child cover mode or validation invariant failed."
        }
    } elseif ($result.Contains('multi_cover') -or
        $result.Contains('cover_validation_fail')) {
        throw "Child $Child baseline unexpectedly enabled multi-edge cover."
    }
    return $result
}

function Assert-FrozenArtifacts {
    foreach ($entry in $expectedHashes.GetEnumerator()) {
        if (-not (Test-Path -LiteralPath $entry.Key -PathType Leaf)) {
            throw "Missing frozen artifact: $($entry.Key)"
        }
        $actualHash = (Get-FileHash -LiteralPath $entry.Key `
            -Algorithm SHA256).Hash
        if ($actualHash -cne $entry.Value) {
            throw "Hash mismatch for $($entry.Key): $actualHash"
        }
    }
}
Assert-FrozenArtifacts

if (Test-Path -LiteralPath 'C:\Ruby33-x64\msys64\ucrt64\bin') {
    $env:Path = 'C:\Ruby33-x64\msys64\ucrt64\bin;' +
        'C:\Ruby33-x64\msys64\usr\bin;' + $env:Path
}

if ($AggregateOnly) {
    if (-not (Test-Path -LiteralPath $runDir -PathType Container)) {
        throw "No profile directory exists: $runDir"
    }
    $expectedCsvPaths = @(0..22 | ForEach-Object {
        (Get-ChildArtifacts $_).csv
    })
    $actualCsvPaths = @(Get-ChildItem -LiteralPath $runDir -File |
        Where-Object {
            $_.Name -like "$ProfileSet.path_2_9_15_*.profile.csv"
        } | ForEach-Object FullName)
    $missing = @($expectedCsvPaths | Where-Object { $_ -notin $actualCsvPaths })
    $unexpected = @($actualCsvPaths | Where-Object {
        $_ -notin $expectedCsvPaths
    })
    if ($missing.Count -or $unexpected.Count -or
        $actualCsvPaths.Count -ne 23) {
        Write-Output "EXPECTED_CHILD_CSV=23 RECORDED=$($actualCsvPaths.Count)"
        if ($missing.Count) {
            $missingNames = @( $missing | ForEach-Object {
                Split-Path -Leaf $_
            } | Sort-Object )
            Write-Output "MISSING=$($missingNames -join ',')"
        }
        if ($unexpected.Count) {
            $unexpectedNames = @( $unexpected | ForEach-Object {
                Split-Path -Leaf $_
            } | Sort-Object )
            Write-Output "UNEXPECTED=$($unexpectedNames -join ',')"
        }
        throw 'The 23-child profile set is incomplete or has extra CSV files.'
    }

    $baselineFrontier = [int64]0
    $coverFrontier = [int64]0
    $baselineNodes = [int64]0
    $coverNodes = [int64]0
    foreach ($child in 0..22) {
        $artifacts = Get-ChildArtifacts $child
        if (-not (Test-Path -LiteralPath $artifacts.lock -PathType Leaf)) {
            throw "Child $child lacks its atomic lock/audit artifact."
        }
        if (-not (Test-Path -LiteralPath $artifacts.log -PathType Leaf)) {
            throw "Child $child lacks its durable profile log."
        }
        $lockLines = @(Get-Content -LiteralPath $artifacts.lock)
        if ($lockLines.Count -ne 4 -or
            $lockLines[0] -cne "profile_set=$ProfileSet" -or
            $lockLines[1] -cne "child=$child" -or
            $lockLines[2] -notmatch '^claimed_local=.+$' -or
            $lockLines[3] -notmatch '^completed_local=.+$') {
            throw "Child $child lock does not record a completed profile."
        }
        $rows = @(Import-Csv -LiteralPath $artifacts.csv)
        if ($rows.Count -ne 2) {
            throw "Child $child CSV has $($rows.Count) rows, expected 2."
        }
        Assert-ExactOrderedStrings `
            @($rows[0].PSObject.Properties.Name) $profileColumns `
            "child $child profile columns"
        for ($index = 0; $index -lt 2; ++$index) {
            $configuration = @('baseline','cover')[$index]
            $row = $rows[$index]
            $arguments = @(Get-Arguments $child $configuration)
            $expectedArguments = $arguments -join ' '
            if ($row.profile_set -cne $ProfileSet -or
                $row.child -cne [string]$child -or
                $row.branch_path -cne "2,9,15,$child" -or
                $row.configuration -cne $configuration -or
                $row.status -cne 'FRONTIER' -or $row.exit_code -cne '0' -or
                $row.solver_sha256 -cne $expectedSolverSha256 -or
                $row.source_sha256 -cne $expectedSourceSha256 -or
                $row.plan_sha256 -cne $expectedPlanSha256 -or
                $row.fanout_sha256 -cne $expectedFanoutSha256 -or
                $row.arguments -cne $expectedArguments) {
                throw "Child $child $configuration CSV binding failed."
            }
            $result = Assert-ProfileResult `
                $child $configuration $row.result_line
            if ($row.nodes -cne $result.nodes -or
                $row.frontier -cne $result.frontier -or
                $row.solution_topologies -cne $result.solution_topologies) {
                throw "Child $child $configuration CSV/result counters differ."
            }
            if ($configuration -eq 'cover') {
                if ($row.multi_cover -cne 'on' -or
                    $row.cover_validation_fail -cne '0') {
                    throw "Child $child cover CSV invariants failed."
                }
            } elseif ($row.multi_cover -cne 'off' -or
                $row.cover_validation_fail -cne 'not_applicable') {
                throw "Child $child baseline CSV invariants failed."
            }
            ConvertTo-StrictPositiveDouble $row.wall_seconds `
                "child $child $configuration wall time" | Out-Null
            $expectedStdoutPath = `
                $artifacts["${configuration}_stdout"]
            $expectedStderrPath = `
                $artifacts["${configuration}_stderr"]
            $expectedDonePath = $artifacts["${configuration}_done"]
            if ($row.stdout_path -cne `
                    (Get-WorkspaceRelativePath $expectedStdoutPath) -or
                $row.stderr_path -cne `
                    (Get-WorkspaceRelativePath $expectedStderrPath) -or
                $row.done_path -cne `
                    (Get-WorkspaceRelativePath $expectedDonePath)) {
                throw "Child $child $configuration raw-artifact binding failed."
            }
            $stdoutPath = Join-Path $rootDir ($row.stdout_path -replace '/', '\')
            $stderrPath = Join-Path $rootDir ($row.stderr_path -replace '/', '\')
            $donePath = Join-Path $rootDir ($row.done_path -replace '/', '\')
            foreach ($path in @($stdoutPath,$stderrPath,$donePath)) {
                if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
                    throw "Child $child $configuration lacks raw artifact $path."
                }
            }
            if ((Get-Item -LiteralPath $stderrPath).Length -ne 0) {
                throw "Child $child $configuration has nonempty stderr."
            }
            $doneKeys = @(
                'exit_code','wall_seconds','started_local','ended_local',
                'solver_sha256','source_sha256','arguments'
            )
            $doneValues = Read-StrictKeyValueFile `
                $donePath $doneKeys "child $child $configuration done"
            if ($doneValues.exit_code -cne '0' -or
                $doneValues.wall_seconds -cne $row.wall_seconds -or
                $doneValues.started_local -cne $row.started_local -or
                $doneValues.ended_local -cne $row.ended_local -or
                $doneValues.solver_sha256 -cne $expectedSolverSha256 -or
                $doneValues.source_sha256 -cne $expectedSourceSha256 -or
                $doneValues.arguments -cne $expectedArguments) {
                throw "Child $child $configuration done/CSV binding failed."
            }
            $rawLines = @(Get-Content -LiteralPath $stdoutPath)
            if ($rawLines.Count -ne 1 -or
                $rawLines[0] -cne $row.result_line) {
                throw "Child $child $configuration raw stdout differs from CSV."
            }
            if ($configuration -eq 'baseline') {
                $baselineFrontier += [int64]$result.frontier
                $baselineNodes += [int64]$result.nodes
            } else {
                $coverFrontier += [int64]$result.frontier
                $coverNodes += [int64]$result.nodes
            }
        }
    }
    # Node sums are diagnostics only: every selected-child run repeats its
    # prefix, so unlike frontiers they must not be compared with the parent.
    Write-Output "CHILDREN=23 BASELINE_NODES_DIAGNOSTIC_SUM=$baselineNodes COVER_NODES_DIAGNOSTIC_SUM=$coverNodes NODE_SUMS_ADDITIVE=NO"
    Write-Output "BASELINE_FRONTIER_SUM=$baselineFrontier TARGET=$targetBaselineFrontier"
    Write-Output "COVER_FRONTIER_SUM=$coverFrontier TARGET=$targetCoverFrontier"
    if ($baselineFrontier -ne $targetBaselineFrontier -or
        $coverFrontier -ne $targetCoverFrontier) {
        throw 'The 23 child frontiers do not reproduce path 2,9,15.'
    }
    Write-Output 'G001_ROW1_PATH_2_9_15_PROFILE_SUM_OK'
    return
}

$rangeArtifacts = @{}
foreach ($child in $FirstChild..$LastChild) {
    $artifacts = Get-ChildArtifacts $child
    $rangeArtifacts[$child] = $artifacts
    foreach ($artifactKey in @($artifacts.Keys | Where-Object {
        $_ -cne 'stem'
    })) {
        $path = $artifacts[$artifactKey]
        if (Test-Path -LiteralPath $path) {
            throw "Refusing to overwrite existing child-$child artifact: $path"
        }
    }
}

if ($DryRun) {
    foreach ($child in $FirstChild..$LastChild) {
        foreach ($configuration in @('baseline','cover')) {
            $arguments = @(Get-Arguments $child $configuration)
            Write-Output "DRY_RUN child=$child configuration=$configuration arguments=$($arguments -join ' ')"
        }
    }
    Write-Output "DRY_RUN_OK range=$FirstChild..$LastChild profile_set=$ProfileSet"
    return
}

New-Item -ItemType Directory -Path $runDir -Force | Out-Null

function Invoke-ChildConfiguration {
    param(
        [int] $Child,
        [string] $Configuration,
        [System.Collections.Specialized.OrderedDictionary] $Artifacts
    )
    # Re-pin immediately before every native process, not merely once when a
    # long or split profiling invocation begins.
    Assert-FrozenArtifacts
    $arguments = @(Get-Arguments $Child $Configuration)
    $argumentLine = $arguments -join ' '
    $stdoutPath = $Artifacts["${Configuration}_stdout"]
    $stderrPath = $Artifacts["${Configuration}_stderr"]
    $donePath = $Artifacts["${Configuration}_done"]
    $doneTmpPath = $Artifacts["${Configuration}_done_tmp"]
    $started = [DateTimeOffset]::Now.ToString('o')
    Add-Content -LiteralPath $Artifacts.log -Value @(
        "START configuration=$Configuration started_local=$started",
        "arguments=$argumentLine"
    )
    $watch = [Diagnostics.Stopwatch]::StartNew()
    $exitCode = -999
    try {
        & $solver @arguments 1> $stdoutPath 2> $stderrPath
        $exitCode = $LASTEXITCODE
    } catch {
        ($_ | Out-String) | Add-Content -LiteralPath $stderrPath
        $exitCode = -998
    } finally {
        $watch.Stop()
    }
    $ended = [DateTimeOffset]::Now.ToString('o')
    $wallText = $watch.Elapsed.TotalSeconds.ToString(
        'R', [Globalization.CultureInfo]::InvariantCulture)
    Set-Content -LiteralPath $doneTmpPath -Value @(
        "exit_code=$exitCode",
        "wall_seconds=$wallText",
        "started_local=$started",
        "ended_local=$ended",
        "solver_sha256=$expectedSolverSha256",
        "source_sha256=$expectedSourceSha256",
        "arguments=$argumentLine"
    )
    Move-Item -LiteralPath $doneTmpPath -Destination $donePath
    Add-Content -LiteralPath $Artifacts.log -Value `
        "END configuration=$Configuration exit_code=$exitCode wall_seconds=$wallText ended_local=$ended"

    if ($exitCode -ne 0) {
        throw "Child $Child $Configuration exited $exitCode."
    }
    if ((Get-Item -LiteralPath $stderrPath).Length -ne 0) {
        throw "Child $Child $Configuration produced nonempty stderr."
    }
    $resultLines = @(Get-Content -LiteralPath $stdoutPath)
    if ($resultLines.Count -ne 1) {
        throw "Child $Child $Configuration produced $($resultLines.Count) stdout lines."
    }
    $resultLine = $resultLines[0]
    $result = Assert-ProfileResult $Child $Configuration $resultLine
    $multiCover = if ($Configuration -eq 'cover') { 'on' } else { 'off' }
    $validation = if ($Configuration -eq 'cover') {
        $result.cover_validation_fail
    } else { 'not_applicable' }
    $row = [pscustomobject][ordered]@{
        profile_set = $ProfileSet
        child = [string]$Child
        branch_path = "2,9,15,$Child"
        configuration = $Configuration
        status = $result.status
        exit_code = [string]$exitCode
        wall_seconds = $wallText
        nodes = $result.nodes
        frontier = $result.frontier
        solution_topologies = $result.solution_topologies
        multi_cover = $multiCover
        cover_validation_fail = $validation
        solver_sha256 = $expectedSolverSha256
        source_sha256 = $expectedSourceSha256
        plan_sha256 = $expectedPlanSha256
        fanout_sha256 = $expectedFanoutSha256
        arguments = $argumentLine
        result_line = $resultLine
        stdout_path = Get-WorkspaceRelativePath $stdoutPath
        stderr_path = Get-WorkspaceRelativePath $stderrPath
        done_path = Get-WorkspaceRelativePath $donePath
        started_local = $started
        ended_local = $ended
    }
    if ($Configuration -eq 'baseline') {
        $row | Export-Csv -LiteralPath $Artifacts.csv -NoTypeInformation
    } else {
        $row | Export-Csv -LiteralPath $Artifacts.csv `
            -NoTypeInformation -Append
    }
    Add-Content -LiteralPath $Artifacts.log -Value `
        "RESULT configuration=$Configuration $resultLine"
}

foreach ($child in $FirstChild..$LastChild) {
    $artifacts = $rangeArtifacts[$child]
    $lockStream = $null
    try {
        $lockStream = [IO.File]::Open(
            $artifacts.lock,
            [IO.FileMode]::CreateNew,
            [IO.FileAccess]::Write,
            [IO.FileShare]::None)
        $lockWriter = [IO.StreamWriter]::new($lockStream)
        $lockWriter.WriteLine("profile_set=$ProfileSet")
        $lockWriter.WriteLine("child=$child")
        $lockWriter.WriteLine(
            "claimed_local=$([DateTimeOffset]::Now.ToString('o'))")
        $lockWriter.Flush()
        $lockWriter.Dispose()
        $lockStream = $null
    } finally {
        if ($null -ne $lockStream) { $lockStream.Dispose() }
    }
    Set-Content -LiteralPath $artifacts.log -Value @(
        "PROFILE_SET=$ProfileSet",
        "CHILD=$child",
        "BRANCH_PATH=2,9,15,$child",
        "SOLVER_SHA256=$expectedSolverSha256",
        "SOURCE_SHA256=$expectedSourceSha256",
        "PLAN_SHA256=$expectedPlanSha256",
        "FANOUT_SHA256=$expectedFanoutSha256"
    )
    Invoke-ChildConfiguration $child 'baseline' $artifacts
    Invoke-ChildConfiguration $child 'cover' $artifacts
    $rows = @(Import-Csv -LiteralPath $artifacts.csv)
    if ($rows.Count -ne 2 -or
        $rows[0].configuration -cne 'baseline' -or
        $rows[1].configuration -cne 'cover') {
        throw "Child $child did not record its exact baseline/cover pair."
    }
    Add-Content -LiteralPath $artifacts.lock -Value `
        "completed_local=$([DateTimeOffset]::Now.ToString('o'))"
    Write-Output "PROFILED child=$child baseline_frontier=$($rows[0].frontier) cover_frontier=$($rows[1].frontier)"
}

Write-Output "PROFILE_RANGE_COMPLETE profile_set=$ProfileSet range=$FirstChild..$LastChild"
Write-Output "Run -ProfileSet $ProfileSet -AggregateOnly after all 23 children finish."
