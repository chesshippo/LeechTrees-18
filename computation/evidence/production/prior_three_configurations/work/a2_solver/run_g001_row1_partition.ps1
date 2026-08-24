param(
    [Parameter(Mandatory = $true)] [string] $JobName,
    [string] $BranchPath = '',
    [int] $RootBranch = -1
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$solver = Join-Path $solverDir 'order18_topology_free_search_row1.exe'
$source = Join-Path $solverDir 'order18_topology_free_search_row1_snapshot.cpp'
$runDir = Join-Path $solverDir 'row1_partition_runs'
New-Item -ItemType Directory -Force -Path $runDir | Out-Null
$expectedSolverHash = '5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD'
$expectedSourceHash = '134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9'

if (($BranchPath -ne '') -eq ($RootBranch -ge 0)) {
    throw 'Supply exactly one of BranchPath or RootBranch.'
}
if (-not (Test-Path -LiteralPath $solver -PathType Leaf)) {
    throw "Missing solver: $solver"
}
if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
    throw "Missing source snapshot: $source"
}
if ($RootBranch -ge 0 -and ($RootBranch -lt 0 -or $RootBranch -gt 2)) {
    throw 'RootBranch must be in 0..2.'
}
if ($BranchPath -and
    $BranchPath -notmatch '^(?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*))*$') {
    throw 'BranchPath must contain canonical nonnegative integers without leading zeros.'
}
if ($BranchPath) {
    $first = [int]($BranchPath.Split(',')[0])
    if ($first -lt 0 -or $first -gt 2) {
        throw 'The first BranchPath index must be in 0..2.'
    }
}

$solverHash = (Get-FileHash -LiteralPath $solver -Algorithm SHA256).Hash
$sourceHash = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash
if ($solverHash -ne $expectedSolverHash) {
    throw "Unexpected row-1 solver hash: $solverHash"
}
if ($sourceHash -ne $expectedSourceHash) {
    throw "Unexpected row-1 source hash: $sourceHash"
}

$safeName = $JobName -replace '[^A-Za-z0-9_.-]', '_'
$stdout = Join-Path $runDir ($safeName + '.stdout.txt')
$stderr = Join-Path $runDir ($safeName + '.stderr.txt')
$done = Join-Path $runDir ($safeName + '.done.txt')
$doneTmp = Join-Path $runDir ($safeName + '.done.tmp')
$pidFile = Join-Path $runDir ($safeName + '.pid.txt')
$workerFile = Join-Path $runDir ($safeName + '.worker.ps1')

foreach ($path in @($stdout, $stderr, $done, $doneTmp, $pidFile, $workerFile)) {
    if (Test-Path -LiteralPath $path) {
        throw "Refusing to overwrite an existing job artifact: $path"
    }
}

$arguments = @('--mode', 'g001_row1')
if ($BranchPath) {
    $arguments += @('--branch-path', $BranchPath)
} else {
    $arguments += @('--root-branch', [string]$RootBranch)
}
$arguments += @(
    '--multi-edge-cover',
    '--multi-edge-cover-no-hall',
    '--multi-edge-cover-max-components', '6',
    '--multi-edge-cover-budget', '100',
    '--multi-edge-cover-no-exact-hall'
)

$quotedArgs = ($arguments | ForEach-Object {
    "'" + ($_ -replace "'", "''") + "'"
}) -join ','
$started = [DateTimeOffset]::Now.ToString('o')

$worker = @"
`$ErrorActionPreference='Stop'
`$env:Path='C:\Ruby33-x64\msys64\ucrt64\bin;C:\Ruby33-x64\msys64\usr\bin;'+`$env:Path
`$watch=[Diagnostics.Stopwatch]::StartNew()
`$exitCode=-999
try {
    & '$solver' @($quotedArgs) 1> '$stdout' 2> '$stderr'
    `$exitCode=`$LASTEXITCODE
} catch {
    (`$_ | Out-String) | Add-Content -LiteralPath '$stderr'
    `$exitCode=-998
} finally {
    `$watch.Stop()
    Set-Content -LiteralPath '$doneTmp' -Value @(
        "exit_code=`$exitCode",
        "wall_seconds=`$(`$watch.Elapsed.TotalSeconds)",
        "ended_local=`$([DateTimeOffset]::Now.ToString('o'))"
    )
    Move-Item -LiteralPath '$doneTmp' -Destination '$done'
}
"@

Set-Content -LiteralPath $workerFile -Value $worker
$process = Start-Process -FilePath 'powershell.exe' -WindowStyle Hidden `
    -ArgumentList @('-NoLogo','-NoProfile','-NonInteractive','-File',$workerFile) `
    -PassThru

Set-Content -LiteralPath $pidFile -Value @(
    "worker_pid=$($process.Id)",
    "started_local=$started",
    "solver_sha256=$solverHash",
    "source_sha256=$sourceHash",
    "arguments=$($arguments -join ' ')"
)

Write-Output "STARTED job=$safeName worker_pid=$($process.Id)"
Write-Output "stdout=$stdout"
Write-Output "stderr=$stderr"
Write-Output "done=$done"
Write-Output "pid_file=$pidFile"
