param(
    [Parameter(Mandatory = $true)] [string] $JobName,
    [Parameter(Mandatory = $true)] [ValidateSet('a2_attached','a2_separate')] [string] $Mode,
    [string] $BranchPath = '',
    [int] $RootBranch = -1
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$solver = Join-Path $solverDir 'a2_topology_free_search_multicover.exe'
$runDir = Join-Path $solverDir 'partition_runs'
New-Item -ItemType Directory -Force -Path $runDir | Out-Null

$safeName = $JobName -replace '[^A-Za-z0-9_.-]', '_'
$stdout = Join-Path $runDir ($safeName + '.out.txt')
$stderr = Join-Path $runDir ($safeName + '.err.txt')
$done = Join-Path $runDir ($safeName + '.done.txt')
$pidFile = Join-Path $runDir ($safeName + '.pid.txt')

$arguments = @('--mode', $Mode)
if ($BranchPath) {
    $arguments += @('--branch-path', $BranchPath)
} elseif ($RootBranch -ge 0) {
    $arguments += @('--root-branch', [string]$RootBranch)
} else {
    throw 'Supply BranchPath or RootBranch.'
}
$arguments += @(
    '--multi-edge-cover',
    '--multi-edge-cover-no-hall',
    '--multi-edge-cover-budget', '100',
    '--multi-edge-cover-no-exact-hall'
)

$quotedArgs = ($arguments | ForEach-Object {
    "'" + ($_ -replace "'", "''") + "'"
}) -join ','
$worker = @"
`$env:Path='C:\Ruby33-x64\msys64\ucrt64\bin;C:\Ruby33-x64\msys64\usr\bin;'+`$env:Path
`$watch=[Diagnostics.Stopwatch]::StartNew()
& '$solver' @($quotedArgs) 1> '$stdout' 2> '$stderr'
`$code=`$LASTEXITCODE
`$watch.Stop()
Set-Content -LiteralPath '$done' -Value @("exit_code=`$code","wall_seconds=`$(`$watch.Elapsed.TotalSeconds)")
"@
$encoded = [Convert]::ToBase64String([Text.Encoding]::Unicode.GetBytes($worker))
$process = Start-Process -FilePath 'powershell.exe' -WindowStyle Hidden -ArgumentList @(
    '-NoLogo','-NoProfile','-NonInteractive','-EncodedCommand',$encoded
) -PassThru
Set-Content -LiteralPath $pidFile -Value @(
    "worker_pid=$($process.Id)",
    "started_utc=$([DateTime]::UtcNow.ToString('o'))",
    "mode=$Mode",
    "branch_path=$BranchPath",
    "root_branch=$RootBranch"
)

Write-Output "STARTED job=$safeName pid=$($process.Id)"
Write-Output "stdout=$stdout"
Write-Output "stderr=$stderr"
Write-Output "done=$done"
Write-Output "pid_file=$pidFile"
