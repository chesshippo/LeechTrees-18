param(
    [Parameter(Mandatory = $true)] [string] $JobName,
    [Parameter(Mandatory = $true)] [string] $Key,
    [Parameter(Mandatory = $true)] [string] $Selector
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$runDir = Join-Path $solverDir 'row1_partition_runs'
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
$ledger = Join-Path $rootDir 'outputs\G001_ROW1_PARTITION_RESULTS.csv'
$solver = Join-Path $solverDir 'order18_topology_free_search_row1.exe'
$source = Join-Path $solverDir 'order18_topology_free_search_row1_snapshot.cpp'
$expectedSolverHash = '5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD'
$expectedSourceHash = '134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9'
$safeName = $JobName -replace '[^A-Za-z0-9_.-]', '_'
$stdout = Join-Path $runDir ($safeName + '.stdout.txt')
$stderr = Join-Path $runDir ($safeName + '.stderr.txt')
$done = Join-Path $runDir ($safeName + '.done.txt')
$pidFile = Join-Path $runDir ($safeName + '.pid.txt')

foreach ($path in @($stdout, $stderr, $done, $pidFile)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Missing required artifact: $path"
    }
}

$existing = if (Test-Path -LiteralPath $ledger -PathType Leaf) {
    @(Import-Csv -LiteralPath $ledger)
} else { @() }
if (@($existing | Where-Object key -eq $Key).Count) {
    throw "Ledger key already exists: $Key"
}
if (@($existing | Where-Object selector -eq $Selector).Count) {
    throw "Ledger selector already exists: $Selector"
}

$selectorArguments = $null
$expectedKey = $null
if ($Selector -match '^root:([0-2])$') {
    $index = $matches[1]
    $expectedKey = "root_$index"
    $selectorArguments = "--root-branch $index"
} elseif ($Selector -match '^path:((?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*))*)$') {
    $path = $matches[1]
    $first = [int]($path.Split(',')[0])
    if ($first -lt 0 -or $first -gt 2) {
        throw "Path selector begins outside 0..2: $Selector"
    }
    $expectedKey = 'path_' + $path.Replace(',','_')
    $selectorArguments = "--branch-path $path"
} else {
    throw "Invalid selector syntax: $Selector"
}
if ($Key -ne $expectedKey) {
    throw "Key/selector mismatch: expected $expectedKey for $Selector"
}

$doneValues = @{}
foreach ($line in Get-Content -LiteralPath $done) {
    if ($line -match '^([^=]+)=(.*)$') { $doneValues[$matches[1]] = $matches[2] }
}
if (-not $doneValues.ContainsKey('exit_code') -or
    -not $doneValues.ContainsKey('wall_seconds')) {
    throw "Incomplete done artifact: $done"
}

$resultLines = @(Get-Content -LiteralPath $stdout |
    Where-Object { $_ -match '^RESULT mode=g001_row1 ' })
if ($resultLines.Count -ne 1) {
    throw "Expected exactly one row-1 RESULT in $stdout"
}
$result = @{}
foreach ($match in [regex]::Matches(
    $resultLines[0], '(?:^|\s)([A-Za-z0-9_]+)=([^\s]+)')) {
    $result[$match.Groups[1].Value] = $match.Groups[2].Value
}
foreach ($required in @(
    'status','nodes','states','generated','solution_topologies','frontier',
    'multi_cover','cover_validation_fail')) {
    if (-not $result.ContainsKey($required)) {
        throw "RESULT lacks $required"
    }
}
if ($result.status -ne 'ZERO' -or
    [int]$doneValues.exit_code -ne 0 -or
    [int]$result.solution_topologies -ne 0 -or
    [int64]$result.frontier -ne 0) {
    throw "Job is not exhaustive ZERO: status=$($result.status) exit=$($doneValues.exit_code) solutions=$($result.solution_topologies) frontier=$($result.frontier)"
}
if ($result.multi_cover -ne 'on' -or
    [int64]$result.cover_validation_fail -ne 0) {
    throw "Required exact-cover mode/validation invariant failed"
}
if ([int64]$result.nodes -le 0 -or [int64]$result.states -le 0 -or
    [int64]$result.generated -le 0 -or
    [double]$doneValues.wall_seconds -le 0) {
    throw 'Nonpositive production counter or wall time'
}
if ((Get-Item -LiteralPath $stderr).Length -ne 0) {
    throw "Solver stderr is nonempty: $stderr"
}

$pidValues = @{}
foreach ($line in Get-Content -LiteralPath $pidFile) {
    if ($line -match '^([^=]+)=(.*)$') { $pidValues[$matches[1]] = $matches[2] }
}
foreach ($required in @('solver_sha256','source_sha256','arguments')) {
    if (-not $pidValues.ContainsKey($required)) {
        throw "PID metadata lacks ${required}: $pidFile"
    }
}
if ($pidValues.solver_sha256 -ne $expectedSolverHash) {
    throw "Unexpected solver hash: $($pidValues.solver_sha256)"
}
if ($pidValues.source_sha256 -ne $expectedSourceHash) {
    throw "Unexpected source hash: $($pidValues.source_sha256)"
}
$expectedArguments = "--mode g001_row1 $selectorArguments --multi-edge-cover --multi-edge-cover-no-hall --multi-edge-cover-max-components 6 --multi-edge-cover-budget 100 --multi-edge-cover-no-exact-hall"
if ($pidValues.arguments -ne $expectedArguments) {
    throw "Unexpected production arguments: $($pidValues.arguments)"
}
if ((Get-FileHash -LiteralPath $solver -Algorithm SHA256).Hash -ne
    $expectedSolverHash) {
    throw 'Current row-1 executable no longer matches the production hash'
}
if ((Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash -ne
    $expectedSourceHash) {
    throw 'Current row-1 source snapshot no longer matches the production hash'
}

function Get-WorkspaceRelativePath {
    param([string] $Path)
    $absolute = (Resolve-Path -LiteralPath $Path).Path
    $prefix = $rootDir.TrimEnd('\') + '\'
    if (-not $absolute.StartsWith(
        $prefix,[StringComparison]::OrdinalIgnoreCase)) {
        throw "Artifact is outside workspace root: $absolute"
    }
    return $absolute.Substring($prefix.Length).Replace('\','/')
}

$row = [pscustomobject][ordered]@{
    key = $Key
    selector = $Selector
    status = $result.status
    exit_code = [int]$doneValues.exit_code
    nodes = [int64]$result.nodes
    states = [int64]$result.states
    generated = [int64]$result.generated
    wall_seconds = [double]$doneValues.wall_seconds
    stdout_path = Get-WorkspaceRelativePath $stdout
    stderr_path = Get-WorkspaceRelativePath $stderr
    solver_sha256 = $pidValues.solver_sha256
    arguments = $pidValues.arguments
    notes = 'uncapped; production exact-cover flags; stderr empty'
}
$row | Export-Csv -LiteralPath $ledger -NoTypeInformation -Append
$row | Format-List
