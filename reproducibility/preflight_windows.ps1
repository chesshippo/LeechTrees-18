[CmdletBinding()]
param(
    [string]$PythonExecutable = 'python.exe',
    [string]$Cxx = '',
    [string]$RepositoryRoot = '',
    [switch]$SkipRoster,
    [switch]$AllowUnpinnedCompiler
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

function Fail([string]$Message) {
    throw "LEECH18_WINDOWS_PREFLIGHT_FAIL: $Message"
}

if ($env:OS -ne 'Windows_NT') {
    Fail 'Windows is required for the preserved Configurations 2, 3, and 8 executables'
}

$psVersion = $PSVersionTable.PSVersion
if (!(($psVersion.Major -eq 5 -and $psVersion.Minor -ge 1) -or $psVersion.Major -ge 7)) {
    Fail "supported PowerShell is Windows PowerShell 5.1 or PowerShell 7; found $psVersion"
}

if ([string]::IsNullOrWhiteSpace($RepositoryRoot)) {
    $RepositoryRoot = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
} else {
    $RepositoryRoot = [System.IO.Path]::GetFullPath($RepositoryRoot)
}
if (!(Test-Path -LiteralPath $RepositoryRoot -PathType Container)) {
    Fail "repository root is missing: $RepositoryRoot"
}

$pythonCommand = Get-Command -Name $PythonExecutable -CommandType Application -ErrorAction Stop
$pythonPath = $pythonCommand.Source
$versionOutput = (& $pythonPath --version 2>&1 | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $versionOutput -notmatch '^Python (\d+\.\d+\.\d+)') {
    Fail "could not determine Python version from $pythonPath"
}
$pythonVersion = [version]$Matches[1]
if ($pythonVersion -lt [version]'3.12.0') {
    Fail "Python 3.12 or newer is required; found $pythonVersion"
}

$required = @(
    'reproducibility\environment.lock.json',
    'scripts\recompute_prior_three_full.py',
    'scripts\recompute_prior_three_from_source.py',
    'proof\verify_end_to_end.ps1',
    'computation\evidence\production\prior_three_configurations\work\a2_solver\order18_topology_free_search_row1.exe',
    'computation\evidence\production\prior_three_configurations\work\a2_solver\a2_topology_free_search_multicover.exe',
    'computation\evidence\production\prior_three_configurations\work\a2_solver\order18_topology_free_search.exe'
)
foreach ($relative in $required) {
    $path = Join-Path $RepositoryRoot $relative
    if (!(Test-Path -LiteralPath $path -PathType Leaf)) {
        Fail "required file is missing: $relative"
    }
}

Write-Output "WINDOWS_OS=$([System.Environment]::OSVersion.VersionString)"
Write-Output "POWERSHELL_VERSION=$psVersion"
Write-Output "PYTHON_EXECUTABLE=$pythonPath"
Write-Output "PYTHON_VERSION=$pythonVersion"
Write-Output "REPOSITORY_ROOT=$RepositoryRoot"
if ($RepositoryRoot.Length -gt 80) {
    Write-Warning 'The repository path is long. A short path such as C:\leech18 is recommended for the retained legacy coverage scripts.'
}

if (!$SkipRoster) {
    Push-Location $RepositoryRoot
    try {
        & $pythonPath -E -s -S -B .\scripts\recompute_prior_three_full.py --list-only
        if ($LASTEXITCODE -ne 0) {
            Fail "prior-three roster validation exited $LASTEXITCODE"
        }
    } finally {
        Pop-Location
    }
}

$sourceBuildChecked = $false
if (![string]::IsNullOrWhiteSpace($Cxx)) {
    $cxxCommand = Get-Command -Name $Cxx -CommandType Application -ErrorAction Stop
    $sourceArguments = @(
        '-E', '-s', '-S', '-B',
        '.\scripts\recompute_prior_three_from_source.py',
        '--cxx', $cxxCommand.Source,
        '--preflight'
    )
    if ($AllowUnpinnedCompiler) {
        $sourceArguments += '--allow-unpinned-compiler'
    }
    Push-Location $RepositoryRoot
    try {
        & $pythonPath @sourceArguments
        if ($LASTEXITCODE -ne 0) {
            Fail "prior-three source-build preflight exited $LASTEXITCODE"
        }
        $sourceBuildChecked = $true
    } finally {
        Pop-Location
    }
}

Write-Output "LEECH18_WINDOWS_PREFLIGHT_OK python=$pythonVersion powershell=$psVersion roster_checked=$(!$SkipRoster) source_build_checked=$sourceBuildChecked"
