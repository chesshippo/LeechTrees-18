[CmdletBinding()]
param(
    [switch]$StopAfterDescriptors,
    [string]$BaselineLeanLib = '',
    [string]$RunRoot = ''
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$LeanElaborationThreads = 1

$BridgeDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$EndToEndDir = Split-Path -Parent $BridgeDir
$WorkspaceRoot = Split-Path -Parent $EndToEndDir
$RecordPath = Join-Path $BridgeDir 'SEMANTIC_BRIDGE_RECORD.json'
$VerifierPath = Join-Path $BridgeDir 'verify_semantic_bridge.py'
$LeanSource = Join-Path $BridgeDir 'LeanRowSemanticBridge.lean'

function Require-Condition {
    param([bool]$Condition, [string]$Message)
    if (-not $Condition) { throw $Message }
}

function Require-PlainDirectoryAncestry {
    param([string]$Path, [string]$Label)
    $full = [IO.Path]::GetFullPath($Path)
    $current = $full
    while ($true) {
        $item = Get-Item -Force -LiteralPath $current
        Require-Condition (
            $item.PSIsContainer -and
            ($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0
        ) "$Label ancestry is not a plain directory: $current"
        $parent = Split-Path -Parent $current
        if ([string]::IsNullOrEmpty($parent) -or $parent -eq $current) { break }
        $current = $parent
    }
    return $full
}

function Require-PlainSingleLinkFile {
    param([string]$Path, [string]$Label)
    $full = [IO.Path]::GetFullPath($Path)
    $null = Require-PlainDirectoryAncestry -Path (Split-Path -Parent $full) `
        -Label "$Label parent"
    Require-Condition (Test-Path -LiteralPath $full -PathType Leaf) `
        "$Label is missing: $full"
    $item = Get-Item -Force -LiteralPath $full
    $linkType = $item.PSObject.Properties['LinkType']
    Require-Condition (
        -not $item.PSIsContainer -and
        ($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0 -and
        $null -ne $linkType -and
        [string]::IsNullOrEmpty([string]$linkType.Value)
    ) "$Label is linked or its hard-link state is unauditable: $full"
}

$null = Require-PlainDirectoryAncestry -Path $BridgeDir `
    -Label 'Semantic bridge source directory'
Require-PlainSingleLinkFile -Path $MyInvocation.MyCommand.Path `
    -Label 'Semantic bridge wrapper'

$RunStamp = (Get-Date).ToString('yyyyMMdd_HHmmss_fff') + "_pid$PID"
if ([string]::IsNullOrWhiteSpace($RunRoot)) {
    $RunRoot = Join-Path $BridgeDir ".run\$RunStamp"
} elseif (-not [IO.Path]::IsPathRooted($RunRoot)) {
    $RunRoot = Join-Path $WorkspaceRoot $RunRoot
}
$RunRoot = [IO.Path]::GetFullPath($RunRoot)
$endToEndPrefix = [IO.Path]::GetFullPath($EndToEndDir).TrimEnd('\') + '\'
if ($RunRoot.StartsWith(
        $endToEndPrefix, [StringComparison]::OrdinalIgnoreCase)) {
    $runRelativeParts = @([regex]::Split(
        $RunRoot.Substring($endToEndPrefix.Length), '[\\/]'
    ))
    Require-Condition (
        @($runRelativeParts | Where-Object { $_ -ieq '.run' }).Count -gt 0
    ) 'A semantic RunRoot inside proof must be below a .run segment'
}
$existingRunRoot = Get-Item -Force -LiteralPath $RunRoot -ErrorAction SilentlyContinue
Require-Condition ($null -eq $existingRunRoot) `
    "RunRoot already exists; refusing possible stale artifacts: $RunRoot"
$runRootParent = Split-Path -Parent $RunRoot
$existingRunRootParent = Get-Item -Force -LiteralPath $runRootParent `
    -ErrorAction SilentlyContinue
if ($null -eq $existingRunRootParent) {
    $null = Require-PlainDirectoryAncestry `
        -Path (Split-Path -Parent $runRootParent) `
        -Label 'Semantic bridge RunRoot grandparent'
    New-Item -ItemType Directory -Path $runRootParent | Out-Null
}
$null = Require-PlainDirectoryAncestry -Path $runRootParent `
    -Label 'Semantic bridge RunRoot parent'
$LogRoot = Join-Path $RunRoot 'logs'
New-Item -ItemType Directory -Path $LogRoot -Force | Out-Null
$null = Require-PlainDirectoryAncestry -Path $RunRoot `
    -Label 'Semantic bridge RunRoot'
$null = Require-PlainDirectoryAncestry -Path $LogRoot `
    -Label 'Semantic bridge log directory'

function Assert-LeanMemoryGate {
    $leanProcesses = @(Get-Process -ErrorAction SilentlyContinue | Where-Object {
        $_.ProcessName -match '^(lean|lake)$'
    })
    Require-Condition ($leanProcesses.Count -eq 0) 'Another Lean/Lake process is active'
    $os = Get-CimInstance Win32_OperatingSystem
    $total = [double]$os.TotalVisibleMemorySize
    $free = [double]$os.FreePhysicalMemory
    $usedPercent = 100.0 * ($total - $free) / $total
    Write-Host ('CHECK MEMORY GATE used_percent={0:F2}' -f $usedPercent)
    Require-Condition ($usedPercent -lt 90.0) `
        'Physical RAM is at or above the strict 90% Lean launch gate'
}

function Invoke-Captured {
    param(
        [string]$Name,
        [string]$Command,
        [string[]]$Arguments,
        [string]$WorkingDirectory,
        [string]$ExpectedMarker = '',
        [string]$ExpectedUniqueLastMarker = '',
        [switch]$RequireEmptyStderr
    )
    $stdoutPath = Join-Path $LogRoot "$Name.stdout.txt"
    $stderrPath = Join-Path $LogRoot "$Name.stderr.txt"
    foreach ($logTarget in @($stdoutPath, $stderrPath)) {
        Require-Condition (
            $null -eq (Get-Item -Force -LiteralPath $logTarget `
                -ErrorAction SilentlyContinue)
        ) "$Name log target already exists; refusing to overwrite: $logTarget"
    }
    Write-Host "BEGIN $Name"
    $nativeArguments = @($Arguments | ForEach-Object {
        Require-Condition (-not $_.Contains('"')) `
            "$Name argument contains an unsupported quote"
        if ($_ -match '\s') { '"' + $_ + '"' } else { $_ }
    })
    $process = Start-Process -FilePath $Command `
        -ArgumentList $nativeArguments `
        -WorkingDirectory $WorkingDirectory `
        -RedirectStandardOutput $stdoutPath `
        -RedirectStandardError $stderrPath `
        -WindowStyle Hidden -PassThru -Wait
    try {
        $exitCode = $process.ExitCode
    } finally {
        $process.Dispose()
    }
    Require-PlainSingleLinkFile -Path $stdoutPath -Label "$Name stdout"
    Require-PlainSingleLinkFile -Path $stderrPath -Label "$Name stderr"
    $stdout = if ((Get-Item -LiteralPath $stdoutPath).Length -gt 0) {
        Get-Content -Raw -LiteralPath $stdoutPath
    } else { '' }
    $stderr = if ((Get-Item -LiteralPath $stderrPath).Length -gt 0) {
        Get-Content -Raw -LiteralPath $stderrPath
    } else { '' }
    if ($stdout.Length -gt 0) { Write-Host $stdout.TrimEnd("`r", "`n") }
    if ($stderr.Length -gt 0) {
        Write-Host 'STDERR_BEGIN'
        Write-Host $stderr.TrimEnd("`r", "`n")
        Write-Host 'STDERR_END'
    }
    Write-Host "EXIT_CODE $exitCode"
    Require-Condition ($exitCode -eq 0) "$Name exited $exitCode"
    if ($ExpectedMarker.Length -gt 0) {
        Require-Condition $stdout.Contains($ExpectedMarker) `
            "$Name did not print required marker: $ExpectedMarker"
    }
    if ($ExpectedUniqueLastMarker.Length -gt 0) {
        $normalized = ($stdout -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10)
        $lines = @($normalized.Split("`n"))
        Require-Condition (
            $lines.Count -gt 0 -and
            $lines[-1] -ceq $ExpectedUniqueLastMarker
        ) "$Name did not print its required marker as the exact last line"
        Require-Condition (
            @($lines | Where-Object { $_ -ceq $ExpectedUniqueLastMarker }).Count -eq 1
        ) "$Name did not print its required marker exactly once"
    }
    if ($RequireEmptyStderr) {
        Require-Condition ($stderr.Length -eq 0) "$Name wrote to stderr"
    }
    Write-Host "END $Name"
    return @{ StdoutPath = $stdoutPath; Stdout = $stdout }
}

Require-PlainSingleLinkFile -Path $RecordPath `
    -Label 'SEMANTIC_BRIDGE_RECORD.json'
$recordSha256BeforeStaticCheck = (Get-FileHash -Algorithm SHA256 `
    -LiteralPath $RecordPath).Hash.ToLowerInvariant()
Require-PlainSingleLinkFile -Path $VerifierPath `
    -Label 'verify_semantic_bridge.py'
Require-PlainSingleLinkFile -Path $LeanSource `
    -Label 'LeanRowSemanticBridge.lean'
$null = Require-PlainDirectoryAncestry `
    -Path (Join-Path $BridgeDir 'SemanticBridge') `
    -Label 'Semantic bridge module source directory'
$unexpectedBridgeArtifacts = [System.Collections.Generic.List[string]]::new()
$sourceDirectories = [System.Collections.Generic.Stack[System.IO.DirectoryInfo]]::new()
$sourceDirectories.Push((Get-Item -Force -LiteralPath $BridgeDir))
while ($sourceDirectories.Count -gt 0) {
    $sourceDirectory = $sourceDirectories.Pop()
    foreach ($sourceEntry in Get-ChildItem -LiteralPath $sourceDirectory.FullName -Force) {
        Require-Condition (
            ($sourceEntry.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0
        ) "Semantic bridge source tree contains a link: $($sourceEntry.FullName)"
        if ($sourceEntry.Name -ieq '.run') {
            Require-Condition $sourceEntry.PSIsContainer `
                'Semantic bridge .run entry is not a plain directory'
            continue
        }
        if ($sourceEntry.PSIsContainer) {
            $sourceDirectories.Push($sourceEntry)
        }
        elseif ($sourceEntry.Extension -in @('.olean', '.ilean')) {
            $unexpectedBridgeArtifacts.Add($sourceEntry.FullName)
        }
    }
}
Require-Condition ($unexpectedBridgeArtifacts.Count -eq 0) `
    'Found a bridge olean/ilean outside the isolated .run directory'

$python = (Get-Command python.exe -ErrorAction Stop).Source
$explicitBaseline = -not [string]::IsNullOrWhiteSpace($BaselineLeanLib)
$prebuiltPolicyArgs = @()
if ($explicitBaseline) { $prebuiltPolicyArgs += '--skip-prebuilt-dossier' }
Invoke-Captured -Name 'static_source_bridge' -Command $python `
    -Arguments (@('-E', '-s', '-S', '-B', $VerifierPath,
        '--static-only') + $prebuiltPolicyArgs) `
    -WorkingDirectory $WorkspaceRoot `
    -ExpectedUniqueLastMarker 'LEECH18_SEMANTIC_BRIDGE_STATIC_OK rows=8 lean_elaboration=NOT_CHECKED' `
    -RequireEmptyStderr | Out-Null
Require-Condition (
    (Get-FileHash -Algorithm SHA256 -LiteralPath $RecordPath).Hash.ToLowerInvariant() -ceq
    $recordSha256BeforeStaticCheck
) 'Semantic bridge record changed while the strict static checker was running'
$recordRaw = Get-Content -Raw -LiteralPath $RecordPath
Require-Condition (
    (Get-FileHash -Algorithm SHA256 -LiteralPath $RecordPath).Hash.ToLowerInvariant() -ceq
    $recordSha256BeforeStaticCheck
) 'Semantic bridge record changed while PowerShell was reading it'
$record = $recordRaw | ConvertFrom-Json
Require-Condition ($record.schema -eq 'leech18-semantic-bridge-v1') `
    'Unexpected semantic bridge record schema'
$legacy = Join-Path $WorkspaceRoot $record.lean_environment.repository
if (-not $explicitBaseline) {
    $BaselineLeanLib = Join-Path $legacy '.lake\build_release_clean\lib\lean'
} elseif (-not [IO.Path]::IsPathRooted($BaselineLeanLib)) {
    $BaselineLeanLib = Join-Path $WorkspaceRoot $BaselineLeanLib
}
$BaselineLeanLib = Require-PlainDirectoryAncestry -Path $BaselineLeanLib `
    -Label 'Baseline Lean library'

$baselineProject = $BaselineLeanLib
while (-not (Test-Path -LiteralPath (Join-Path $baselineProject 'lake-manifest.json') `
        -PathType Leaf)) {
    $parent = Split-Path -Parent $baselineProject
    Require-Condition ($parent -and $parent -ne $baselineProject) `
        "Could not locate the baseline project above: $BaselineLeanLib"
    $baselineProject = $parent
}

$baselineDossierOlean = Join-Path $BaselineLeanLib `
    'LeechTrees\Expanded\FirstEdge\FirstEdgeDossier.olean'
Require-PlainSingleLinkFile -Path $baselineDossierOlean `
    -Label 'Baseline dossier olean'
$baselineDossierHash = (Get-FileHash -Algorithm SHA256 `
    -LiteralPath $baselineDossierOlean).Hash.ToLowerInvariant()

if ($explicitBaseline) {
    $freshBindings = @(
        @{ Role = 'lean_toolchain'; Relative = 'lean-toolchain' },
        @{ Role = 'lakefile'; Relative = 'lakefile.toml' },
        @{ Role = 'lake_manifest'; Relative = 'lake-manifest.json' },
        @{ Role = 'authoritative_lean_dossier'; Relative =
            'LeechTrees\Expanded\FirstEdge\FirstEdgeDossier.lean' }
    )
    foreach ($binding in $freshBindings) {
        $freshPath = Join-Path $baselineProject $binding.Relative
        Require-PlainSingleLinkFile -Path $freshPath `
            -Label "Fresh baseline input $($binding.Role)"
        $freshHash = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $freshPath).Hash.ToLowerInvariant()
        $expectedHash = $record.inputs.($binding.Role).sha256.ToLowerInvariant()
        Require-Condition ($freshHash -eq $expectedHash) `
            "Fresh baseline hash mismatch for $($binding.Role): $freshHash"
    }
    Write-Host "CHECK FRESH BASELINE SOURCE HASHES OK $baselineProject"
} else {
    $expectedDossierHash = `
        $record.inputs.authoritative_dossier_olean.sha256.ToLowerInvariant()
    Require-Condition ($baselineDossierHash -eq $expectedDossierHash) `
        "Standalone baseline dossier olean hash mismatch: $baselineDossierHash"
}
Write-Host "CHECK BASELINE DOSSIER OLEAN sha256=$baselineDossierHash path=$baselineDossierOlean"

$lean = Join-Path $env:USERPROFILE '.elan\bin\lean.exe'
Require-Condition (Test-Path -LiteralPath $lean -PathType Leaf) `
    "Lean executable is missing: $lean"

$oldToolchain = $env:ELAN_TOOLCHAIN
$oldLeanPath = $env:LEAN_PATH
$oldNoBytecode = $env:PYTHONDONTWRITEBYTECODE
$oldPythonUtf8 = $env:PYTHONUTF8
$leanInjectionNames = @(
    'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN', 'LAKE_OVERRIDE_LEAN'
)
$oldLeanInjection = @{}
foreach ($name in $leanInjectionNames) {
    $oldLeanInjection[$name] = [Environment]::GetEnvironmentVariable(
        $name, [EnvironmentVariableTarget]::Process)
    [Environment]::SetEnvironmentVariable(
        $name, $null, [EnvironmentVariableTarget]::Process)
}
$gitInjectionNames = @(Get-ChildItem Env: | Where-Object {
    $_.Name -like 'GIT_*'
} | Select-Object -ExpandProperty Name)
$oldGitInjection = @{}
foreach ($name in $gitInjectionNames) {
    $oldGitInjection[$name] = [Environment]::GetEnvironmentVariable(
        $name, [EnvironmentVariableTarget]::Process)
    [Environment]::SetEnvironmentVariable(
        $name, $null, [EnvironmentVariableTarget]::Process)
}
$pythonInjectionNames = @(
    'PYTHONHOME', 'PYTHONPATH', 'PYTHONSTARTUP', 'PYTHONINSPECT',
    'PYTHONUSERBASE'
)
$oldPythonInjection = @{}
foreach ($name in $pythonInjectionNames) {
    $oldPythonInjection[$name] = [Environment]::GetEnvironmentVariable(
        $name, [EnvironmentVariableTarget]::Process)
    [Environment]::SetEnvironmentVariable(
        $name, $null, [EnvironmentVariableTarget]::Process)
}
$env:ELAN_TOOLCHAIN = $record.lean_environment.toolchain
$env:PYTHONDONTWRITEBYTECODE = '1'
$env:PYTHONUTF8 = '1'
try {
    Assert-LeanMemoryGate
    Invoke-Captured -Name 'lean_version' -Command $lean `
        -Arguments @('--version') -WorkingDirectory $baselineProject `
        -ExpectedMarker 'version 4.24.0' -RequireEmptyStderr | Out-Null

    if (-not $explicitBaseline) {
        $git = (Get-Command git.exe -ErrorAction Stop).Source
        $head = (& $git -C $legacy rev-parse HEAD).Trim()
        Require-Condition ($LASTEXITCODE -eq 0) `
            'git rev-parse failed for the Lean repository'
        Require-Condition ($head -eq $record.lean_environment.commit) `
            "Lean repository commit mismatch: expected $($record.lean_environment.commit), got $head"
        Write-Host "CHECK LEAN COMMIT OK $head"
    }

    $buildRoot = Join-Path $RunRoot 'lean_build'
    New-Item -ItemType Directory -Path $buildRoot | Out-Null
    $moduleBuildRoot = Join-Path $buildRoot 'SemanticBridge'
    New-Item -ItemType Directory -Path $moduleBuildRoot | Out-Null

    $leanPaths = @($BaselineLeanLib, $buildRoot)
    $lakeManifest = Get-Content -Raw `
        -LiteralPath (Join-Path $baselineProject 'lake-manifest.json') |
        ConvertFrom-Json
    $packageRoot = Join-Path $baselineProject '.lake\packages'
    foreach ($package in $lakeManifest.packages) {
        $candidate = Join-Path (Join-Path $packageRoot $package.name) '.lake\build\lib\lean'
        if (Test-Path -LiteralPath $candidate -PathType Container) {
            $leanPaths += $candidate
        }
    }
    $env:LEAN_PATH = $leanPaths -join ';'

    $modulePlan = @(
        @{ Name = 'descriptor_data'; File = 'DescriptorData.lean' },
        @{ Name = 'descriptor_well_formed'; File = 'DescriptorWellFormed.lean' },
        @{ Name = 'row_core'; File = 'RowCore.lean' },
        @{ Name = 'adjacent_rows'; File = 'AdjacentRows.lean' },
        @{ Name = 'disjoint_rows'; File = 'DisjointRows.lean' },
        @{ Name = 'a2_split'; File = 'A2Split.lean' },
        @{ Name = 'aggregate'; File = 'Aggregate.lean' }
    )
    foreach ($module in $modulePlan) {
        Assert-LeanMemoryGate
        $moduleSource = Join-Path (Join-Path $BridgeDir 'SemanticBridge') $module.File
        $moduleOlean = Join-Path $moduleBuildRoot ($module.File -replace '\.lean$', '.olean')
        Invoke-Captured -Name ("lean_" + $module.Name) -Command $lean `
            -Arguments @(
                '-j', [string]$LeanElaborationThreads,
                $moduleSource, '-o', $moduleOlean
            ) `
            -WorkingDirectory $BridgeDir -RequireEmptyStderr | Out-Null
        Require-Condition (Test-Path -LiteralPath $moduleOlean -PathType Leaf) `
            "Lean did not create the fresh module artifact: $moduleOlean"
        if ($StopAfterDescriptors -and $module.Name -eq 'descriptor_well_formed') {
            Write-Host "RUN_DIRECTORY $RunRoot"
            Write-Host 'LEECH18_SEMANTIC_BRIDGE_DESCRIPTOR_STAGE_OK modules=2'
            return
        }
    }

    Assert-LeanMemoryGate
    $umbrellaOlean = Join-Path $buildRoot 'LeanRowSemanticBridge.olean'
    $leanResult = Invoke-Captured -Name 'lean_semantic_bridge' -Command $lean `
        -Arguments @(
            '-j', [string]$LeanElaborationThreads,
            $LeanSource, '-o', $umbrellaOlean
        ) `
        -WorkingDirectory $BridgeDir -RequireEmptyStderr
    Require-Condition (Test-Path -LiteralPath $umbrellaOlean -PathType Leaf) `
        "Lean did not create the fresh umbrella artifact: $umbrellaOlean"

    $fullResult = Invoke-Captured -Name 'full_semantic_bridge' -Command $python `
        -Arguments (@('-E', '-s', '-S', '-B', $VerifierPath,
            '--lean-output', $leanResult.StdoutPath) + $prebuiltPolicyArgs) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedUniqueLastMarker 'LEECH18_SEMANTIC_BRIDGE_OK rows=8 direct=7 projected=1' `
        -RequireEmptyStderr
    Require-Condition (-not $fullResult.Stdout.Contains(
        'LEECH18_SEMANTIC_BRIDGE_STATIC_OK')) `
        'Full semantic bridge output contained the static-only marker'

    $runPrefix = $RunRoot.TrimEnd('\') + '\'
    $artifactPaths = @()
    foreach ($module in $modulePlan) {
        $artifactPaths += Join-Path $moduleBuildRoot `
            ($module.File -replace '\.lean$', '.olean')
    }
    $artifactPaths += $umbrellaOlean
    $artifactRecords = @($artifactPaths | ForEach-Object {
        Require-PlainSingleLinkFile -Path $_ -Label 'Semantic bridge artifact'
        [ordered]@{
            path = $_.Substring($runPrefix.Length).Replace('\', '/')
            sha256 = (Get-FileHash -Algorithm SHA256 `
                -LiteralPath $_).Hash.ToLowerInvariant()
        }
    })
    $expectedLogNames = @(
        'full_semantic_bridge',
        'lean_a2_split',
        'lean_adjacent_rows',
        'lean_aggregate',
        'lean_descriptor_data',
        'lean_descriptor_well_formed',
        'lean_disjoint_rows',
        'lean_row_core',
        'lean_semantic_bridge',
        'lean_version',
        'static_source_bridge'
    ) | ForEach-Object { ($_ + '.stdout.txt'); ($_ + '.stderr.txt') }
    $logEntries = @(Get-ChildItem -LiteralPath $LogRoot -Force | Sort-Object Name)
    Require-Condition (
        (@($logEntries.Name) -join "`n") -ceq
        (@($expectedLogNames | Sort-Object) -join "`n")
    ) 'Semantic bridge log directory exact-set mismatch'
    $logRecords = @($logEntries | ForEach-Object {
            Require-PlainSingleLinkFile -Path $_.FullName `
                -Label 'Semantic bridge log'
            [ordered]@{
                path = $_.FullName.Substring($runPrefix.Length).Replace('\', '/')
                sha256 = (Get-FileHash -Algorithm SHA256 `
                    -LiteralPath $_.FullName).Hash.ToLowerInvariant()
            }
        })
    $bridgePrefix = $BridgeDir.TrimEnd('\') + '\'
    $bridgeSourcePaths = @(
        (Join-Path $BridgeDir 'README.md'),
        $RecordPath,
        $VerifierPath,
        (Join-Path $BridgeDir 'verify_semantic_bridge.ps1'),
        $LeanSource
    )
    foreach ($module in $modulePlan) {
        $bridgeSourcePaths += Join-Path `
            (Join-Path $BridgeDir 'SemanticBridge') $module.File
    }
    $bridgeSourceRecords = @($bridgeSourcePaths | Sort-Object | ForEach-Object {
        Require-PlainSingleLinkFile -Path $_ -Label 'Semantic bridge source'
        [ordered]@{
            path = $_.Substring($bridgePrefix.Length).Replace('\', '/')
            sha256 = (Get-FileHash -Algorithm SHA256 `
                -LiteralPath $_).Hash.ToLowerInvariant()
        }
    })
    $inputRecords = @($record.inputs.PSObject.Properties |
        Sort-Object Name | ForEach-Object {
            [ordered]@{
                role = $_.Name
                path = $_.Value.path.Replace('\', '/')
                sha256 = $_.Value.sha256.ToLowerInvariant()
            }
        })
    $terminalMarker = `
        'LEECH18_SEMANTIC_BRIDGE_REPLAY_OK rows=8 direct=7 projected=1'
    $runResult = [ordered]@{
        schema = 'leech18-semantic-bridge-run-result-v1'
        status = 'PASS'
        terminal_marker = $terminalMarker
        baseline_mode = if ($explicitBaseline) { 'explicit_fresh' } `
            else { 'standalone_pinned' }
        baseline_dossier_olean_sha256 = $baselineDossierHash
        lean_elaboration_threads = $LeanElaborationThreads
        lean_toolchain = $record.lean_environment.toolchain
        lean_source_commit = $record.lean_environment.commit
        record_sha256 = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $RecordPath).Hash.ToLowerInvariant()
        lean_emitter_stdout_sha256 = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $leanResult.StdoutPath).Hash.ToLowerInvariant()
        full_checker_stdout_sha256 = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $fullResult.StdoutPath).Hash.ToLowerInvariant()
        axiom_audit_declarations = @(
            'Leech18SemanticBridge.rowDescriptors_all_wellFormed',
            'Leech18SemanticBridge.eightRowDossier_implies_some_realized_core',
            'Leech18SemanticBridge.isLeech_implies_some_realized_seed_descriptor',
            'Leech18SemanticBridge.adjacentMeetsTwoRow_implies_a2_production_split'
        )
        axiom_allowlist = @('Classical.choice', 'Quot.sound', 'propext')
        bridge_sources = $bridgeSourceRecords
        pinned_inputs = $inputRecords
        artifacts = $artifactRecords
        logs = $logRecords
    }
    $runResultPath = Join-Path $RunRoot 'RUN_RESULT.json'
    $runResultJson = $runResult | ConvertTo-Json -Depth 6
    foreach ($forbiddenRoot in @(
        $RunRoot, $WorkspaceRoot, $BaselineLeanLib, $baselineProject,
        $env:USERPROFILE, $env:HOME, $env:LOCALAPPDATA, $env:APPDATA,
        $env:TEMP, $env:TMP
    )) {
        if (-not [string]::IsNullOrWhiteSpace($forbiddenRoot)) {
            Require-Condition (
                $runResultJson.IndexOf(
                    [string]$forbiddenRoot,
                    [StringComparison]::OrdinalIgnoreCase
                ) -lt 0
            ) 'Semantic bridge RUN_RESULT contains an absolute host-root string'
        }
    }
    foreach ($absolutePathPattern in @(
        '(?i)(?:\\\\\?\\)?[a-z]:[\\/]',
        '(?i)(?:^|[\s=''\"])/(?:home|users|private|tmp)/',
        '(?i)\\\\[^\\\s]+\\[^\\\s]+'
    )) {
        Require-Condition (-not [regex]::IsMatch(
            $runResultJson, $absolutePathPattern
        )) 'Semantic bridge RUN_RESULT contains an absolute host path'
    }
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $runResultPath `
            -ErrorAction SilentlyContinue)
    ) 'Semantic bridge RUN_RESULT.json already exists'
    [IO.File]::WriteAllText(
        $runResultPath, $runResultJson + [Environment]::NewLine,
        [Text.UTF8Encoding]::new($false))
    $runResultHash = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $runResultPath).Hash.ToLowerInvariant()
    $runResultSidecar = Join-Path $RunRoot 'RUN_RESULT.sha256'
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $runResultSidecar `
            -ErrorAction SilentlyContinue)
    ) 'Semantic bridge RUN_RESULT.sha256 already exists'
    [IO.File]::WriteAllText(
        $runResultSidecar, "$runResultHash  RUN_RESULT.json`n",
        [Text.UTF8Encoding]::new($false))
    Require-PlainSingleLinkFile -Path $runResultPath `
        -Label 'Semantic bridge RUN_RESULT.json'
    Require-PlainSingleLinkFile -Path $runResultSidecar `
        -Label 'Semantic bridge RUN_RESULT.sha256'
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $runResultPath).Hash.ToLowerInvariant() -ceq
        $runResultHash
    ) 'Semantic bridge RUN_RESULT.json changed before publication'
    Require-Condition (
        (Get-Content -Raw -LiteralPath $runResultSidecar) -ceq
        "$runResultHash  RUN_RESULT.json`n"
    ) 'Semantic bridge RUN_RESULT sidecar changed before publication'
    $semanticRootEntries = @(
        Get-ChildItem -Force -LiteralPath $RunRoot |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    Require-Condition (
        ($semanticRootEntries -join "`n") -ceq
        (@('lean_build', 'logs', 'RUN_RESULT.json', 'RUN_RESULT.sha256') -join "`n")
    ) 'Semantic bridge run-root exact-set mismatch'
    $semanticBuildRootEntries = @(
        Get-ChildItem -Force -LiteralPath $buildRoot |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    Require-Condition (
        ($semanticBuildRootEntries -join "`n") -ceq
        (@('LeanRowSemanticBridge.olean', 'SemanticBridge') -join "`n")
    ) 'Semantic bridge lean-build root exact-set mismatch'
    $semanticModuleEntries = @(
        Get-ChildItem -Force -LiteralPath $moduleBuildRoot |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    $expectedSemanticModuleEntries = @(
        $modulePlan | ForEach-Object { $_.File -replace '\.lean$', '.olean' } |
            Sort-Object
    )
    Require-Condition (
        ($semanticModuleEntries -join "`n") -ceq
        ($expectedSemanticModuleEntries -join "`n")
    ) 'Semantic bridge module-build exact-set mismatch'
    foreach ($semanticOutputDirectory in @($buildRoot, $moduleBuildRoot, $LogRoot)) {
        $semanticOutputDirectoryInfo = Get-Item -Force -LiteralPath $semanticOutputDirectory
        Require-Condition (
            $semanticOutputDirectoryInfo.PSIsContainer -and
            ($semanticOutputDirectoryInfo.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0
        ) "Semantic bridge output directory is linked: $semanticOutputDirectory"
    }
    foreach ($semanticArtifactRecord in $artifactRecords) {
        $semanticArtifactPath = Join-Path $RunRoot `
            ($semanticArtifactRecord.path -replace '/', '\')
        Require-PlainSingleLinkFile -Path $semanticArtifactPath `
            -Label 'Final semantic bridge artifact'
        Require-Condition (
            (Get-FileHash -Algorithm SHA256 -LiteralPath $semanticArtifactPath).Hash.ToLowerInvariant() -ceq
            [string]$semanticArtifactRecord.sha256
        ) "Semantic bridge artifact changed before publication: $($semanticArtifactRecord.path)"
    }
    foreach ($semanticLogRecord in $logRecords) {
        $semanticLogPath = Join-Path $RunRoot `
            ($semanticLogRecord.path -replace '/', '\')
        Require-PlainSingleLinkFile -Path $semanticLogPath `
            -Label 'Final semantic bridge log'
        Require-Condition (
            (Get-FileHash -Algorithm SHA256 -LiteralPath $semanticLogPath).Hash.ToLowerInvariant() -ceq
            [string]$semanticLogRecord.sha256
        ) "Semantic bridge log changed before publication: $($semanticLogRecord.path)"
    }
    Write-Host "RUN_DIRECTORY $RunRoot"
    Write-Host "RUN_RESULT_JSON $runResultPath sha256=$runResultHash sidecar=$runResultSidecar"
    Write-Host $terminalMarker
}
finally {
    $env:ELAN_TOOLCHAIN = $oldToolchain
    $env:LEAN_PATH = $oldLeanPath
    $env:PYTHONDONTWRITEBYTECODE = $oldNoBytecode
    $env:PYTHONUTF8 = $oldPythonUtf8
    foreach ($name in $pythonInjectionNames) {
        [Environment]::SetEnvironmentVariable(
            $name, $oldPythonInjection[$name],
            [EnvironmentVariableTarget]::Process)
    }
    foreach ($name in $gitInjectionNames) {
        [Environment]::SetEnvironmentVariable(
            $name, $oldGitInjection[$name],
            [EnvironmentVariableTarget]::Process)
    }
    foreach ($name in $leanInjectionNames) {
        [Environment]::SetEnvironmentVariable(
            $name, $oldLeanInjection[$name],
            [EnvironmentVariableTarget]::Process)
    }
}
