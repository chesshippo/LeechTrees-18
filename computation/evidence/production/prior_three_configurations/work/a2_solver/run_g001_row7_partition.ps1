param(
    [Parameter(Mandatory = $true)] [string] $JobName,
    [string] $BranchPath = '',
    [int] $RootBranch = -1,
    [int] $StopEdges = -1
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$solver = Join-Path $solverDir 'order18_topology_free_search.exe'
$runDir = Join-Path $solverDir 'row7_partition_runs'
New-Item -ItemType Directory -Force -Path $runDir | Out-Null

if (($BranchPath -ne '') -eq ($RootBranch -ge 0)) {
    throw 'Supply exactly one of BranchPath or RootBranch.'
}
if (-not (Test-Path -LiteralPath $solver -PathType Leaf)) {
    throw "Missing solver: $solver"
}

$safeName = $JobName -replace '[^A-Za-z0-9_.-]', '_'
$stdout = Join-Path $runDir ($safeName + '.stdout.txt')
$stderr = Join-Path $runDir ($safeName + '.stderr.txt')
$done = Join-Path $runDir ($safeName + '.done.txt')
$pidFile = Join-Path $runDir ($safeName + '.pid.txt')
$workerFile = Join-Path $runDir ($safeName + '.worker.ps1')

foreach ($path in @($stdout, $stderr, $done, $pidFile, $workerFile)) {
    if (Test-Path -LiteralPath $path) {
        throw "Refusing to overwrite an existing job artifact: $path"
    }
}

$arguments = @('--mode', 'g001_row7')
if ($BranchPath) {
    $arguments += @('--branch-path', $BranchPath)
} else {
    $arguments += @('--root-branch', [string]$RootBranch)
}
if ($StopEdges -ge 0) {
    $arguments += @('--stop-edges', [string]$StopEdges)
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
$solverHash = (Get-FileHash -LiteralPath $solver -Algorithm SHA256).Hash
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
    Set-Content -LiteralPath '$done' -Value @(
        "exit_code=`$exitCode",
        "wall_seconds=`$(`$watch.Elapsed.TotalSeconds)",
        "ended_local=`$([DateTimeOffset]::Now.ToString('o'))"
    )
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
    "arguments=$($arguments -join ' ')"
)

Write-Output "STARTED job=$safeName worker_pid=$($process.Id)"
Write-Output "stdout=$stdout"
Write-Output "stderr=$stderr"
Write-Output "done=$done"
Write-Output "pid_file=$pidFile"
