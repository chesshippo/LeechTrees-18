param(
    [Parameter(Mandatory = $true)] [string] $JobName,
    [Parameter(Mandatory = $true)] [string] $Key,
    [Parameter(Mandatory = $true)] [string] $Selector
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$runDir = Join-Path $solverDir 'row7_partition_runs'
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
$ledger = Join-Path $rootDir 'outputs\G001_ROW7_PARTITION_RESULTS.csv'
$safeName = $JobName -replace '[^A-Za-z0-9_.-]', '_'
$stdout = Join-Path $runDir ($safeName + '.stdout.txt')
$stderr = Join-Path $runDir ($safeName + '.stderr.txt')
$done = Join-Path $runDir ($safeName + '.done.txt')
$pidFile = Join-Path $runDir ($safeName + '.pid.txt')

foreach ($path in @($stdout, $stderr, $done, $pidFile, $ledger)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Missing required artifact: $path"
    }
}

$existing = @(Import-Csv -LiteralPath $ledger)
if (@($existing | Where-Object key -eq $Key).Count) {
    throw "Ledger key already exists: $Key"
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
    Where-Object { $_ -match '^RESULT mode=g001_row7 ' })
if ($resultLines.Count -ne 1) {
    throw "Expected exactly one row-7 RESULT in $stdout"
}
$result = @{}
foreach ($match in [regex]::Matches($resultLines[0], '(?:^|\s)([A-Za-z0-9_]+)=([^\s]+)')) {
    $result[$match.Groups[1].Value] = $match.Groups[2].Value
}
foreach ($required in @('status','nodes','states','generated','solution_topologies')) {
    if (-not $result.ContainsKey($required)) {
        throw "RESULT lacks $required"
    }
}
if ($result.status -ne 'ZERO' -or
    [int]$doneValues.exit_code -ne 0 -or
    [int]$result.solution_topologies -ne 0) {
    throw "Job is not a terminal exhaustive ZERO: status=$($result.status) exit=$($doneValues.exit_code) solutions=$($result.solution_topologies)"
}

$pidValues = @{}
foreach ($line in Get-Content -LiteralPath $pidFile) {
    if ($line -match '^([^=]+)=(.*)$') { $pidValues[$matches[1]] = $matches[2] }
}
if (-not $pidValues.ContainsKey('solver_sha256')) {
    throw "PID metadata lacks solver_sha256: $pidFile"
}
$stderrLength = (Get-Item -LiteralPath $stderr).Length
$notes = if ($stderrLength -eq 0) {
    'uncapped; production exact-cover flags; stderr empty'
} else {
    "uncapped; production exact-cover flags; stderr bytes=$stderrLength"
}

function Get-WorkspaceRelativePath {
    param([string] $Path)
    $absolute = (Resolve-Path -LiteralPath $Path).Path
    $prefix = $rootDir.TrimEnd('\') + '\'
    if (-not $absolute.StartsWith($prefix,
        [StringComparison]::OrdinalIgnoreCase)) {
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
    notes = $notes
}
$row | Export-Csv -LiteralPath $ledger -NoTypeInformation -Append
$row | Format-List
