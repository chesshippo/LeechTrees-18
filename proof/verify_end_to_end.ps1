[CmdletBinding()]
param(
    [switch]$UseRecordedGlobalReplay,
    [string]$Cxx = 'g++',
    [string]$PythonExecutable = 'python.exe'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$LeanElaborationThreads = 1
$LeanRuntimeThreads = 1

$ProofDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$WorkspaceRoot = Split-Path -Parent $ProofDir
$RecordPath = Join-Path $ProofDir 'HYBRID_PROOF_RECORD.json'
$scriptInfo = Get-Item -Force -LiteralPath $MyInvocation.MyCommand.Path
$scriptLinkType = $scriptInfo.PSObject.Properties['LinkType']
if (($scriptInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0 -or
        $null -eq $scriptLinkType -or
        -not [string]::IsNullOrEmpty([string]$scriptLinkType.Value)) {
    throw "Verifier script is linked or its hard-link state is unauditable: $($MyInvocation.MyCommand.Path)"
}
$proofAncestryPath = [System.IO.Path]::GetFullPath($ProofDir)
while ($true) {
    $proofAncestryInfo = Get-Item -Force -LiteralPath $proofAncestryPath
    if (($proofAncestryInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0) {
        throw "Proof-package ancestry contains a link/reparse point: $proofAncestryPath"
    }
    $proofAncestryParent = Split-Path -Parent $proofAncestryPath
    if ([string]::IsNullOrEmpty($proofAncestryParent) -or
            $proofAncestryParent -eq $proofAncestryPath) {
        break
    }
    $proofAncestryPath = $proofAncestryParent
}
$RunStartedAt = Get-Date
$RunStamp = $RunStartedAt.ToString('yyyyMMdd_HHmmss_fff') + "_pid$PID"
$RunBase = Join-Path $ProofDir '.run'
if (Test-Path -LiteralPath $RunBase) {
    $runBaseInfo = Get-Item -Force -LiteralPath $RunBase
    if (-not $runBaseInfo.PSIsContainer -or
            ($runBaseInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0) {
        throw "Run-output base is not a plain directory: $RunBase"
    }
}
else {
    New-Item -ItemType Directory -Path $RunBase | Out-Null
}
$RunRoot = Join-Path $RunBase $RunStamp
$LogRoot = Join-Path $RunRoot 'logs'
New-Item -ItemType Directory -Path $RunRoot | Out-Null
New-Item -ItemType Directory -Path $LogRoot | Out-Null
$TranscriptPath = Join-Path $RunRoot 'ORCHESTRATOR_TRANSCRIPT.txt'
$TranscriptStarted = $false
$RuntimeSourceReportSha256 = 'NOT_RUN'
$RuntimeSourceManifestSha256 = 'NOT_RUN'
$LeanProjectArchiveSha256 = 'NOT_RUN'
$PythonExecutableSha256 = 'NOT_RUN'
$PowerShellExecutableSha256 = 'NOT_RUN'
$GitExecutableSha256 = 'NOT_RUN'
$TarExecutableSha256 = 'NOT_RUN'
$LeanExecutableSha256 = 'NOT_RUN'
$LakeExecutableSha256 = 'NOT_RUN'
$InitialPackageManifestSha256 = 'NOT_CHECKED'
$Config3RunResultSha256 = 'NOT_RUN'
$Config3ReleaseRecordSha256 = 'NOT_RUN'
$Config3ReleaseManifestSha256 = 'NOT_RUN'
$FreshBaselineLeanLib = $null
$FreshDossierOleanSha256 = 'NOT_RUN'
$SemanticBridgeRecordSha256 = 'NOT_RUN'
$SemanticBridgeRunResultSha256 = 'NOT_RUN'
$SemanticBridgeRunResultSidecarSha256 = 'NOT_RUN'
$SemanticBridgeStdoutSha256 = 'NOT_RUN'
$RegeneratedPlanSha256 = 'NOT_RUN'
$RegeneratedPlanManifestSha256 = 'NOT_RUN'
$RegeneratedPlanReceiptSha256 = 'NOT_RUN'
$StageLogManifestSha256 = 'NOT_RUN'
$TranscriptSha256 = 'NOT_RUN'
$GitExecutablePath = $null
$TarExecutablePath = $null
$RequiredFullStageNames = @(
    'configuration_2',
    'configuration_3',
    'config3_a2_frozen_split_strict',
    'configuration_3_strict_ledger_audit',
    'configuration_8',
    'frozen_runtime_source',
    'global_relocated_collector',
    'hybrid_record',
    'hybrid_record_final',
    'lean_clean_baseline_build',
    'lean_git_archive',
    'lean_git_archive_extract',
    'lean_git_archive_objects',
    'lean_git_tree',
    'lean_hybrid_boundary',
    'lean_version',
    'prior_three_manifest',
    'python_version',
    'semantic_bridge',
    'source_freeze',
    'terminal5_source_tests',
    'terminal_plan',
    'terminal_plan_regeneration_build',
    'terminal_plan_regeneration_compare'
)

function Require-Condition {
    param([bool]$Condition, [string]$Message)
    if (-not $Condition) {
        throw $Message
    }
}

function Require-PlainSingleLinkFile {
    param([string]$Path, [string]$Label)
    $lexicalPath = [System.IO.Path]::GetFullPath($Path)
    $ancestry = Split-Path -Parent $lexicalPath
    while (-not [string]::IsNullOrEmpty($ancestry)) {
        $ancestryInfo = Get-Item -Force -LiteralPath $ancestry
        Require-Condition (
            $ancestryInfo.PSIsContainer -and
            ($ancestryInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
        ) "$Label ancestry is not a plain directory: $ancestry"
        $ancestryParent = Split-Path -Parent $ancestry
        if ([string]::IsNullOrEmpty($ancestryParent) -or $ancestryParent -eq $ancestry) {
            break
        }
        $ancestry = $ancestryParent
    }
    Require-Condition (Test-Path -LiteralPath $Path -PathType Leaf) `
        "$Label is missing: $Path"
    $item = Get-Item -Force -LiteralPath $Path
    Require-Condition (
        -not $item.PSIsContainer -and
        ($item.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
    ) "$Label is not a plain file: $Path"
    $linkTypeProperty = $item.PSObject.Properties['LinkType']
    Require-Condition ($null -ne $linkTypeProperty) `
        'Selected PowerShell cannot expose file link type; refusing an unaudited hard-link state'
    Require-Condition ([string]::IsNullOrEmpty([string]$linkTypeProperty.Value)) `
        "$Label is linked (LinkType=$($linkTypeProperty.Value)): $Path"
}

function Get-NormalizedTextSha256 {
    param([string]$Text)
    $normalized = ($Text -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10)
    $utf8NoBom = New-Object System.Text.UTF8Encoding($false)
    $sha256 = [System.Security.Cryptography.SHA256]::Create()
    try {
        $digest = $sha256.ComputeHash($utf8NoBom.GetBytes($normalized))
        return -join ($digest | ForEach-Object { $_.ToString('x2') })
    }
    finally {
        $sha256.Dispose()
    }
}

function Write-RunResult {
    param(
        [string]$Mode,
        [int]$ExitCode,
        [string]$FinalMarker,
        [string]$Failure = ''
    )
    $manifestPath = Join-Path $ProofDir 'MANIFEST.sha256'
    $manifestHash = if (Test-Path -LiteralPath $manifestPath -PathType Leaf) {
        (Get-FileHash -Algorithm SHA256 -LiteralPath $manifestPath).Hash.ToLowerInvariant()
    } else {
        'UNAVAILABLE'
    }
    $runResult = @(
        "MODE $Mode",
        "EXIT_CODE $ExitCode",
        "FINAL_MARKER $FinalMarker",
        "MANIFEST_SHA256 $manifestHash",
        "INITIAL_MANIFEST_SHA256 $InitialPackageManifestSha256",
        "RUNTIME_SOURCE_REPORT_SHA256 $RuntimeSourceReportSha256",
        "RUNTIME_SOURCE_MANIFEST_SHA256 $RuntimeSourceManifestSha256",
        "LEAN_PROJECT_ARCHIVE_SHA256 $LeanProjectArchiveSha256",
        "PYTHON_EXECUTABLE_SHA256 $PythonExecutableSha256",
        "POWERSHELL_EXECUTABLE_SHA256 $PowerShellExecutableSha256",
        "GIT_EXECUTABLE_SHA256 $GitExecutableSha256",
        "TAR_EXECUTABLE_SHA256 $TarExecutableSha256",
        "LEAN_EXECUTABLE_SHA256 $LeanExecutableSha256",
        "LAKE_EXECUTABLE_SHA256 $LakeExecutableSha256",
        "LEAN_ELABORATION_THREADS $LeanElaborationThreads",
        "LEAN_NUM_THREADS $LeanRuntimeThreads",
        "CONFIG3_RUN_RESULT_SHA256 $Config3RunResultSha256",
        "CONFIG3_RELEASE_RECORD_SHA256 $Config3ReleaseRecordSha256",
        "CONFIG3_RELEASE_MANIFEST_SHA256 $Config3ReleaseManifestSha256",
        "FRESH_DOSSIER_OLEAN_SHA256 $FreshDossierOleanSha256",
        "SEMANTIC_BRIDGE_RECORD_SHA256 $SemanticBridgeRecordSha256",
        "SEMANTIC_BRIDGE_RUN_RESULT_SHA256 $SemanticBridgeRunResultSha256",
        "SEMANTIC_BRIDGE_RUN_RESULT_SIDECAR_SHA256 $SemanticBridgeRunResultSidecarSha256",
        "SEMANTIC_BRIDGE_STDOUT_SHA256 $SemanticBridgeStdoutSha256",
        "REGENERATED_PLAN_SHA256 $RegeneratedPlanSha256",
        "REGENERATED_PLAN_MANIFEST_SHA256 $RegeneratedPlanManifestSha256",
        "REGENERATED_PLAN_RECEIPT_SHA256 $RegeneratedPlanReceiptSha256",
        "STAGE_LOG_MANIFEST_SHA256 $StageLogManifestSha256",
        "TRANSCRIPT_SHA256 $TranscriptSha256",
        'TRANSCRIPT ORCHESTRATOR_TRANSCRIPT.txt',
        "STARTED_AT $($RunStartedAt.ToString('o'))",
        "COMPLETED_AT $((Get-Date).ToString('o'))"
    )
    if ($Failure.Length -gt 0) {
        $safeFailure = [regex]::Replace($Failure, '\s+', ' ').Trim()
        $runResult += "FAILURE $safeFailure"
    }
    $utf8NoBom = New-Object System.Text.UTF8Encoding($false)
    $runResultPath = Join-Path $RunRoot 'RUN_RESULT.txt'
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $runResultPath `
            -ErrorAction SilentlyContinue)
    ) 'RUN_RESULT.txt already exists; refusing to overwrite it'
    [System.IO.File]::WriteAllText(
        $runResultPath,
        (($runResult -join "`n") + "`n"),
        $utf8NoBom
    )
    Require-PlainSingleLinkFile -Path $runResultPath -Label 'RUN_RESULT.txt'
}

function Write-StageLogManifest {
    param([string[]]$ExpectedStages)
    $manifestPath = Join-Path $RunRoot 'STAGE_LOGS.sha256'
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $manifestPath `
            -ErrorAction SilentlyContinue)
    ) `
        'Stage-log manifest already exists'
    $logEntries = @(Get-ChildItem -LiteralPath $LogRoot -Force)
    Require-Condition ($logEntries.Count -gt 0) 'No stage logs were produced'
    $byStage = @{}
    $lines = [System.Collections.Generic.List[string]]::new()
    foreach ($entry in $logEntries) {
        Require-PlainSingleLinkFile -Path $entry.FullName -Label 'Stage log'
        Require-Condition (
            -not $entry.PSIsContainer -and
            ($entry.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0 -and
            $entry.Name -match '^([A-Za-z0-9_.-]+)\.(stdout|stderr)\.txt$'
        ) "Unexpected stage-log entry: $($entry.Name)"
        $stage = $Matches[1]
        $stream = $Matches[2]
        if (-not $byStage.ContainsKey($stage)) {
            $byStage[$stage] = @{}
        }
        Require-Condition (-not $byStage[$stage].ContainsKey($stream)) `
            "Duplicate stage-log stream: $stage $stream"
        $byStage[$stage][$stream] = $true
        $digest = (Get-FileHash -Algorithm SHA256 -LiteralPath $entry.FullName).Hash.ToLowerInvariant()
        $lines.Add("$digest  logs/$($entry.Name)")
    }
    foreach ($stage in $byStage.Keys) {
        Require-Condition (
            $byStage[$stage].ContainsKey('stdout') -and
            $byStage[$stage].ContainsKey('stderr') -and
            $byStage[$stage].Count -eq 2
        ) "Incomplete stage-log pair: $stage"
    }
    $actualStages = @($byStage.Keys | Sort-Object)
    $expectedStageOrder = @($ExpectedStages | Sort-Object)
    Require-Condition (
        ($actualStages -join "`n") -ceq ($expectedStageOrder -join "`n")
    ) "Stage-log roster mismatch: actual=$($actualStages -join ',')"
    $sortedLines = [string[]]$lines.ToArray()
    [System.Array]::Sort($sortedLines, [System.StringComparer]::Ordinal)
    $utf8NoBom = New-Object System.Text.UTF8Encoding($false)
    [System.IO.File]::WriteAllText(
        $manifestPath,
        (($sortedLines -join "`n") + "`n"),
        $utf8NoBom
    )
    Require-PlainSingleLinkFile -Path $manifestPath `
        -Label 'Stage-log manifest'
    return (Get-FileHash -Algorithm SHA256 -LiteralPath $manifestPath).Hash.ToLowerInvariant()
}

function Get-RelativeUnixPath {
    param([string]$Base, [string]$Path)
    $baseUri = [Uri]((Resolve-Path -LiteralPath $Base).Path.TrimEnd('\') + '\')
    $pathUri = [Uri](Resolve-Path -LiteralPath $Path).Path
    return [Uri]::UnescapeDataString($baseUri.MakeRelativeUri($pathUri).ToString())
}

function Get-ExtendedWindowsPath {
    param([string]$Path)
    $full = [System.IO.Path]::GetFullPath($Path)
    if ($full.StartsWith('\\?\')) {
        return $full
    }
    return '\\?\' + $full
}

function Test-PackagePrivacy {
    param([string[]]$RelativeFiles)
    $privateKeyMarker = ('-' * 5) + 'BEGIN ' + 'PRIVATE KEY' + ('-' * 5)
    $privateKeyVariants = @(
        $privateKeyMarker,
        (('-' * 5) + 'BEGIN RSA ' + 'PRIVATE KEY' + ('-' * 5)),
        (('-' * 5) + 'BEGIN OPENSSH ' + 'PRIVATE KEY' + ('-' * 5)),
        (('-' * 5) + 'BEGIN EC ' + 'PRIVATE KEY' + ('-' * 5))
    )
    $credentialPatterns = @(
        '(?im)\b(?:api[_-]?key|access[_-]?token|auth[_-]?token|client[_-]?secret|secret[_-]?key|password)\b\s*[:=]\s*["'']?[A-Za-z0-9_./+=-]{8,}',
        '(?i)\bAKIA[0-9A-Z]{16}\b',
        '(?i)\bgh[pousr]_[A-Za-z0-9]{30,}\b',
        '(?i)\bsk-[A-Za-z0-9]{20,}\b'
    )
    $personalPathPattern = '(?i)(?:[a-z]:[\\/]+users[\\/]+[^\\/\s"'']+|/(?:home|users)/[^/\s"'']+)'
    $decoder = New-Object System.Text.UTF8Encoding($false, $true)
    foreach ($relative in $RelativeFiles) {
        Require-Condition (
            $relative -notmatch '(?i)(^|/)(?:\.env(?:\..*)?|id_(?:rsa|dsa|ecdsa|ed25519)|[^/]+\.(?:pem|p12|pfx|key))$'
        ) "Proof package contains a credential-like filename: $relative"
        $path = Get-ContainedPlainSingleLinkFile -Root $ProofDir `
            -Relative $relative -Label "Proof-package privacy file $relative"
        $raw = [System.IO.File]::ReadAllBytes($path)
        try {
            $text = $decoder.GetString($raw)
        }
        catch {
            throw "Proof package contains a non-UTF-8 publication file: $relative"
        }
        Require-Condition (-not $text.Contains([char]0)) `
            "Proof package contains a NUL byte: $relative"
        Require-Condition (-not [regex]::IsMatch($text, $personalPathPattern)) `
            "Proof package contains an absolute personal path: $relative"
        foreach ($marker in $privateKeyVariants) {
            Require-Condition (-not $text.Contains($marker)) `
                "Proof package contains a private-key marker: $relative"
        }
        foreach ($pattern in $credentialPatterns) {
            Require-Condition (-not [regex]::IsMatch($text, $pattern)) `
                "Proof package contains a credential/token pattern: $relative"
        }
    }
    Write-Host "CHECK PROOF PACKAGE PRIVACY OK files=$($RelativeFiles.Count)"
}

function Test-PackageManifest {
    $manifestPath = Join-Path $ProofDir 'MANIFEST.sha256'
    Require-PlainSingleLinkFile -Path $manifestPath -Label 'MANIFEST.sha256'
    $manifestText = Get-Content -Raw -LiteralPath $manifestPath
    Require-Condition (
        $manifestText.Length -gt 0 -and
        $manifestText.EndsWith("`n") -and
        -not $manifestText.Contains("`r")
    ) 'MANIFEST.sha256 is not canonical LF text'
    $manifestLines = @($manifestText.TrimEnd([char]10).Split("`n"))
    Require-Condition (
        $manifestLines.Count -gt 0 -and
        -not ($manifestLines | Where-Object { [string]::IsNullOrWhiteSpace($_) })
    ) 'MANIFEST.sha256 is empty or contains blank lines'
    $listed = [System.Collections.Generic.Dictionary[string,bool]]::new(
        [System.StringComparer]::OrdinalIgnoreCase
    )
    $manifestRelativeOrder = [System.Collections.Generic.List[string]]::new()
    foreach ($line in $manifestLines) {
        Require-Condition ($line -match '^([0-9a-f]{64})  (.+)$') "Malformed manifest line: $line"
        $expected = $Matches[1]
        $relative = $Matches[2]
        Require-SafeReportRelativePath -Relative $relative -Label 'manifest'
        Require-Condition (
            $relative -notmatch '(?i)(^|/)\.run(/|$)' -and
            $relative -ine 'MANIFEST.sha256'
        ) "Unsafe manifest path: $relative"
        Require-Condition (-not $listed.ContainsKey($relative)) "Duplicate manifest entry: $relative"
        $path = Get-ContainedPlainSingleLinkFile -Root $ProofDir `
            -Relative $relative -Label "Manifest file $relative"
        $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant()
        Require-Condition ($actual -eq $expected) "Manifest hash mismatch: $relative"
        $listed.Add($relative, $true)
        $manifestRelativeOrder.Add($relative)
    }
    $sortedManifestRelativeOrder = [string[]]$manifestRelativeOrder.ToArray()
    [System.Array]::Sort(
        $sortedManifestRelativeOrder,
        [System.StringComparer]::Ordinal
    )
    for ($manifestIndex = 0; $manifestIndex -lt $manifestRelativeOrder.Count; $manifestIndex++) {
        Require-Condition (
            $manifestRelativeOrder[$manifestIndex] -ceq $sortedManifestRelativeOrder[$manifestIndex]
        ) 'MANIFEST.sha256 is not sorted by relative path'
    }
    $actualFileList = [System.Collections.Generic.List[string]]::new()
    $pendingDirectories = [System.Collections.Generic.Stack[System.IO.DirectoryInfo]]::new()
    $pendingDirectories.Push((Get-Item -Force -LiteralPath $ProofDir))
    while ($pendingDirectories.Count -gt 0) {
        $directory = $pendingDirectories.Pop()
        foreach ($entry in Get-ChildItem -LiteralPath $directory.FullName -Force) {
            Require-Condition (
                ($entry.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
            ) "Proof package contains a link/reparse point: $($entry.FullName)"
            $relative = Get-RelativeUnixPath -Base $ProofDir -Path $entry.FullName
            if ($entry.Name -ieq '.run') {
                Require-Condition (
                    $entry.PSIsContainer
                ) "Generated-output .run container is not a plain directory: $relative"
                continue
            }
            if ($entry.PSIsContainer) {
                $pendingDirectories.Push($entry)
            }
            elseif ($entry.FullName -ne $manifestPath) {
                $actualFileList.Add($relative)
            }
        }
    }
    $actualFiles = @($actualFileList)
    foreach ($relative in $actualFiles) {
        Require-Condition $listed.ContainsKey($relative) "Unlisted proof file: $relative"
    }
    Require-Condition ($listed.Count -eq $actualFiles.Count) 'Manifest has an unexpected entry count'
    Test-PackagePrivacy -RelativeFiles (@($actualFiles) + @('MANIFEST.sha256'))
    Write-Host "CHECK PROOF MANIFEST OK files=$($listed.Count)"
}

function Require-SafeReportRelativePath {
    param([string]$Relative, [string]$Label)
    Require-Condition ($null -ne $Relative) "Non-string $Label path"
    $windows = $Relative -replace '/', '\'
    $parts = @([regex]::Split($Relative, '/'))
    Require-Condition (
        $Relative.Length -gt 0 -and
        $Relative -notmatch '\\' -and
        $Relative -notmatch '[\x00-\x1f\x7f]' -and
        $Relative -notmatch ':' -and
        -not [System.IO.Path]::IsPathRooted($windows) -and
        $parts.Count -gt 0 -and
        @($parts | Where-Object {
            $_.Length -eq 0 -or $_ -ceq '.' -or $_ -ceq '..' -or
            $_.EndsWith('.') -or $_.EndsWith(' ') -or
            $_ -match '(?i)^(?:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?$'
        }).Count -eq 0 -and
        $Relative -ceq ($parts -join '/')
    ) "Unsafe $Label path: $Relative"
}

function Get-ContainedPlainSingleLinkFile {
    param([string]$Root, [string]$Relative, [string]$Label)
    Require-SafeReportRelativePath -Relative $Relative -Label $Label
    $rootPath = [System.IO.Path]::GetFullPath($Root).TrimEnd('\')
    $rootAncestry = $rootPath
    while ($true) {
        $rootInfo = Get-Item -Force -LiteralPath $rootAncestry
        Require-Condition (
            $rootInfo.PSIsContainer -and
            ($rootInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
        ) "$Label root ancestry is not a plain directory: $rootAncestry"
        $rootParent = Split-Path -Parent $rootAncestry
        if ([string]::IsNullOrEmpty($rootParent) -or $rootParent -eq $rootAncestry) {
            break
        }
        $rootAncestry = $rootParent
    }
    $parts = @(($Relative -replace '/', '\').Split('\'))
    $current = $rootPath
    for ($index = 0; $index -lt $parts.Count - 1; $index++) {
        $current = Join-Path $current $parts[$index]
        $directoryInfo = Get-Item -Force -LiteralPath $current
        Require-Condition (
            $directoryInfo.PSIsContainer -and
            ($directoryInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
        ) "$Label ancestor is not a plain directory: $current"
    }
    $target = Join-Path $rootPath ($Relative -replace '/', '\')
    Require-PlainSingleLinkFile -Path $target -Label $Label
    $resolvedRootPrefix = (Resolve-Path -LiteralPath $rootPath).Path.TrimEnd('\') + '\'
    $resolvedTarget = (Resolve-Path -LiteralPath $target).Path
    Require-Condition (
        $resolvedTarget.StartsWith(
            $resolvedRootPrefix,
            [System.StringComparison]::OrdinalIgnoreCase
        )
    ) "$Label resolves outside its permitted root: $Relative"
    return $target
}

function Test-ExactPathHashInventory {
    param(
        [object[]]$Records,
        [string[]]$ExpectedPaths,
        [string]$Root,
        [string]$Label,
        [switch]$Rehash
    )
    $observed = [System.Collections.Generic.Dictionary[string,string]]::new(
        [System.StringComparer]::OrdinalIgnoreCase
    )
    foreach ($item in @($Records)) {
        $fields = @($item.PSObject.Properties.Name | Sort-Object)
        Require-Condition (($fields -join ',') -ceq 'path,sha256') `
            "Malformed $Label inventory item"
        $relative = [string]$item.path
        $digest = [string]$item.sha256
        Require-SafeReportRelativePath -Relative $relative -Label $Label
        Require-Condition ($digest -cmatch '^[0-9a-f]{64}$') `
            "Malformed $Label digest: $relative"
        Require-Condition (-not $observed.ContainsKey($relative)) `
            "Duplicate or case-aliased $Label path: $relative"
        $observed.Add($relative, $digest)
        if ($Rehash) {
            $target = Get-ContainedPlainSingleLinkFile `
                -Root $Root -Relative $relative -Label "$Label file"
            $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $target).Hash.ToLowerInvariant()
            Require-Condition ($actual -eq $digest) `
                "$Label digest mismatch: $relative"
        }
    }
    $actualPaths = @($observed.Keys | Sort-Object)
    $expected = @($ExpectedPaths | Sort-Object)
    Require-Condition (
        ($actualPaths -join "`n") -ceq ($expected -join "`n")
    ) "$Label exact-set mismatch: actual=$($actualPaths -join ',')"
    return ,$observed
}

function Invoke-Logged {
    param(
        [string]$Name,
        [string]$Command,
        [string[]]$Arguments,
        [string]$WorkingDirectory,
        [string]$ExpectedMarker = '',
        [string]$ExpectedUniqueLastMarker = '',
        [string]$ExpectedNormalizedStdoutPattern = '',
        [string]$ExpectedNormalizedStdoutSha256 = '',
        [switch]$RequireEmptyStderr
    )
    $safeName = $Name -replace '[^A-Za-z0-9_.-]', '_'
    $stdoutPath = Join-Path $LogRoot "$safeName.stdout.txt"
    $stderrPath = Join-Path $LogRoot "$safeName.stderr.txt"
    foreach ($logTarget in @($stdoutPath, $stderrPath)) {
        Require-Condition (
            $null -eq (Get-Item -Force -LiteralPath $logTarget `
                -ErrorAction SilentlyContinue)
        ) "$Name log target already exists; refusing to overwrite: $logTarget"
    }
    Write-Host "BEGIN $Name"
    Write-Host "WORKING_DIRECTORY $WorkingDirectory"
    Write-Host ("COMMAND " + $Command + ' ' + ($Arguments -join ' '))
    Push-Location -LiteralPath $WorkingDirectory
    try {
        & $Command @Arguments 1> $stdoutPath 2> $stderrPath
        $exitCode = $LASTEXITCODE
    }
    finally {
        Pop-Location
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
    if ($stderr.Length -gt 0) { Write-Host 'STDERR_BEGIN'; Write-Host $stderr.TrimEnd("`r", "`n"); Write-Host 'STDERR_END' }
    Write-Host "EXIT_CODE $exitCode"
    Require-Condition ($exitCode -eq 0) "$Name exited $exitCode"
    if ($ExpectedMarker.Length -gt 0) {
        Require-Condition $stdout.Contains($ExpectedMarker) "$Name did not print its required marker"
    }
    if ($ExpectedUniqueLastMarker.Length -gt 0) {
        $markerNormalized = ($stdout -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10)
        $markerLines = @($markerNormalized.Split("`n"))
        Require-Condition (
            $markerLines.Count -gt 0 -and
            $markerLines[-1] -ceq $ExpectedUniqueLastMarker
        ) "$Name did not print its required marker as the exact last line"
        Require-Condition (
            @($markerLines | Where-Object { $_ -ceq $ExpectedUniqueLastMarker }).Count -eq 1
        ) "$Name printed its required marker more than once"
    }
    if ($ExpectedNormalizedStdoutPattern.Length -gt 0) {
        $normalizedStdout = ($stdout -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10)
        Require-Condition ([regex]::IsMatch($normalizedStdout, $ExpectedNormalizedStdoutPattern)) `
            "$Name normalized stdout did not match its exact pattern"
    }
    if ($ExpectedNormalizedStdoutSha256.Length -gt 0) {
        Require-Condition ($ExpectedNormalizedStdoutSha256 -match '^[0-9a-f]{64}$') `
            "$Name has a malformed expected stdout digest"
        $actualStdoutSha256 = Get-NormalizedTextSha256 -Text $stdout
        Require-Condition ($actualStdoutSha256 -eq $ExpectedNormalizedStdoutSha256) `
            "$Name normalized stdout digest mismatch: $actualStdoutSha256"
    }
    if ($RequireEmptyStderr) {
        Require-Condition ($stderr.Length -eq 0) "$Name wrote to stderr"
    }
    Write-Host "END $Name"
    return $stdout
}

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
    Require-Condition ($usedPercent -lt 90.0) 'Physical RAM is at or above the 90% Lean launch gate'
}

function Build-LeanBoundary {
    param([pscustomobject]$Record)
    Assert-LeanMemoryGate
    $legacy = Join-Path $WorkspaceRoot $Record.lean.repository
    $lake = Join-Path $env:USERPROFILE '.elan\bin\lake.exe'
    $lean = Join-Path $env:USERPROFILE '.elan\bin\lean.exe'
    $git = $script:GitExecutablePath
    $tar = $script:TarExecutablePath
    Require-Condition (Test-Path -LiteralPath $lake -PathType Leaf) "Lake executable is missing: $lake"
    Require-Condition (Test-Path -LiteralPath $lean -PathType Leaf) "Lean executable is missing: $lean"
    Require-Condition (Test-Path -LiteralPath $git -PathType Leaf) "Git executable is missing: $git"
    Require-Condition (Test-Path -LiteralPath $tar -PathType Leaf) "tar executable is missing: $tar"
    $script:LeanExecutableSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $lean).Hash.ToLowerInvariant()
    $script:LakeExecutableSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $lake).Hash.ToLowerInvariant()
    $oldLeanPath = $env:LEAN_PATH
    $oldLeanSrcPath = $env:LEAN_SRC_PATH
    $oldLeanSysroot = $env:LEAN_SYSROOT
    $oldLeanExecutable = $env:LEAN
    $oldLakeOverrideLean = $env:LAKE_OVERRIDE_LEAN
    $oldLeanNumThreads = $env:LEAN_NUM_THREADS

    try {
        $env:LEAN_PATH = $null
        $env:LEAN_SRC_PATH = $null
        $env:LEAN_SYSROOT = $null
        $env:LEAN = $null
        $env:LAKE_OVERRIDE_LEAN = $null
        $env:LEAN_NUM_THREADS = [string]$LeanRuntimeThreads

        Invoke-Logged -Name 'lean_version' -Command $lean -Arguments @('--version') `
            -WorkingDirectory $legacy -ExpectedMarker 'version 4.24.0' `
            -RequireEmptyStderr | Out-Null

    $cleanProject = Join-Path $RunRoot 'lean_project'
    $projectArchive = Join-Path $RunRoot 'lean_project.tar'
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $projectArchive `
            -ErrorAction SilentlyContinue)
    ) 'Pristine Lean project archive target already exists'
    $treeOutput = Invoke-Logged -Name 'lean_git_tree' -Command $git `
        -Arguments @(
            '-C', $legacy, 'ls-tree', '-r', '--full-tree',
            '--format=%(objectmode) %(objecttype) %(objectname)%x09%(path)',
            $Record.lean.commit
        ) `
        -WorkingDirectory $WorkspaceRoot -RequireEmptyStderr
    $treeLines = @(
        (($treeOutput -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10)).Split("`n")
    )
    Require-Condition ($treeLines.Count -gt 0) 'Pinned Lean project tree is empty'
    $expectedArchiveObjects = [System.Collections.Generic.Dictionary[string,string]]::new(
        [System.StringComparer]::OrdinalIgnoreCase
    )
    $trackedPathList = [System.Collections.Generic.List[string]]::new()
    foreach ($line in $treeLines) {
        Require-Condition (
            $line -match '^(100644|100755) blob ([0-9a-f]{40}|[0-9a-f]{64})\t([A-Za-z0-9._/-]+)$'
        ) "Unsupported entry in the pinned Lean project tree: $line"
        $objectHash = $Matches[2]
        $relative = $Matches[3]
        Require-SafeReportRelativePath -Relative $relative `
            -Label 'pinned Lean project tree'
        Require-Condition (-not $expectedArchiveObjects.ContainsKey($relative)) `
            "Duplicate or case-aliased path in the pinned Lean project tree: $relative"
        $expectedArchiveObjects.Add($relative, $objectHash)
        $trackedPathList.Add($relative)
    }

    # Validate every tree path and reject Git symlinks before allowing tar to
    # materialize the archive.  This makes extraction fail closed on path
    # aliases/traversal rather than discovering them only afterward.
    New-Item -ItemType Directory -Path $cleanProject | Out-Null
    Invoke-Logged -Name 'lean_git_archive' -Command $git `
        -Arguments @('-C', $legacy, 'archive', '--format=tar', "--output=$projectArchive", $Record.lean.commit) `
        -WorkingDirectory $WorkspaceRoot -RequireEmptyStderr | Out-Null
    Require-PlainSingleLinkFile -Path $projectArchive `
        -Label 'Pristine Lean project archive'
    $script:LeanProjectArchiveSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $projectArchive).Hash.ToLowerInvariant()
    Invoke-Logged -Name 'lean_git_archive_extract' -Command $tar `
        -Arguments @('-xf', $projectArchive, '-C', $cleanProject) `
        -WorkingDirectory $WorkspaceRoot -RequireEmptyStderr | Out-Null

    $cleanProjectInfo = Get-Item -Force -LiteralPath $cleanProject
    Require-Condition (
        $cleanProjectInfo.PSIsContainer -and
        ($cleanProjectInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
    ) 'Pristine Lean project extraction root is linked or not a directory'
    $archiveEntryList = [System.Collections.Generic.List[System.IO.FileSystemInfo]]::new()
    $archiveDirectoryStack = [System.Collections.Generic.Stack[System.IO.DirectoryInfo]]::new()
    $archiveDirectoryStack.Push($cleanProjectInfo)
    while ($archiveDirectoryStack.Count -gt 0) {
        $archiveDirectory = $archiveDirectoryStack.Pop()
        foreach ($entry in Get-ChildItem -LiteralPath $archiveDirectory.FullName -Force) {
            Require-Condition (
                ($entry.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
            ) "Pristine Lean project archive contains a link/reparse point: $($entry.FullName)"
            $archiveEntryList.Add($entry)
            if ($entry.PSIsContainer) {
                $archiveDirectoryStack.Push($entry)
            }
            else {
                Require-PlainSingleLinkFile -Path $entry.FullName `
                    -Label 'Pristine Lean project archive file'
            }
        }
    }
    $archiveEntries = @($archiveEntryList)
    $archivePaths = @(
        $archiveEntries |
            Where-Object { -not $_.PSIsContainer } |
            ForEach-Object { Get-RelativeUnixPath -Base $cleanProject -Path $_.FullName }
    )
    $trackedPaths = @($trackedPathList)
    Require-Condition ($archivePaths.Count -eq $trackedPaths.Count) `
        'Pristine Lean archive file count differs from the pinned Git tree'
    $archiveSetDifference = @(Compare-Object -ReferenceObject $trackedPaths `
        -DifferenceObject $archivePaths -CaseSensitive)
    Require-Condition ($archiveSetDifference.Count -eq 0) `
        "Pristine Lean archive file set differs from the pinned Git tree: $($archiveSetDifference -join ', ')"

    # Feed paths on stdin: the complete tree is far larger than the Windows
    # command-line limit, so argv expansion would make the clean-build gate
    # host-dependent or fail before checking all blobs.
    $archiveObjectStdout = Join-Path $LogRoot 'lean_git_archive_objects.stdout.txt'
    $archiveObjectStderr = Join-Path $LogRoot 'lean_git_archive_objects.stderr.txt'
    foreach ($archiveObjectLog in @($archiveObjectStdout, $archiveObjectStderr)) {
        Require-Condition (
            $null -eq (Get-Item -Force -LiteralPath $archiveObjectLog `
                -ErrorAction SilentlyContinue)
        ) "Pristine archive object log already exists: $archiveObjectLog"
    }
    Write-Host 'BEGIN lean_git_archive_objects'
    Write-Host "WORKING_DIRECTORY $cleanProject"
    Write-Host "COMMAND $git -C $cleanProject hash-object --no-filters --stdin-paths"
    Push-Location -LiteralPath $cleanProject
    try {
        $archiveObjectHashes = @(
            $trackedPaths | & $git -C $cleanProject hash-object --no-filters --stdin-paths `
                2> $archiveObjectStderr
        )
        $archiveObjectExitCode = $LASTEXITCODE
    }
    finally {
        Pop-Location
    }
    Require-PlainSingleLinkFile -Path $archiveObjectStderr `
        -Label 'Pristine archive object stderr'
    $utf8NoBom = New-Object System.Text.UTF8Encoding($false)
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $archiveObjectStdout `
            -ErrorAction SilentlyContinue)
    ) 'Pristine archive object stdout appeared before publication'
    [System.IO.File]::WriteAllLines(
        $archiveObjectStdout,
        [string[]]$archiveObjectHashes,
        $utf8NoBom
    )
    Require-PlainSingleLinkFile -Path $archiveObjectStdout `
        -Label 'Pristine archive object stdout'
    $archiveObjectError = if ((Get-Item -LiteralPath $archiveObjectStderr).Length -gt 0) {
        Get-Content -Raw -LiteralPath $archiveObjectStderr
    } else { '' }
    if ($archiveObjectError.Length -gt 0) {
        Write-Host 'STDERR_BEGIN'
        Write-Host $archiveObjectError.TrimEnd("`r", "`n")
        Write-Host 'STDERR_END'
    }
    Write-Host "EXIT_CODE $archiveObjectExitCode"
    Require-Condition ($archiveObjectExitCode -eq 0) `
        "lean_git_archive_objects exited $archiveObjectExitCode"
    Require-Condition ($archiveObjectError.Length -eq 0) `
        'lean_git_archive_objects wrote to stderr'
    Write-Host 'END lean_git_archive_objects'
    Require-Condition ($archiveObjectHashes.Count -eq $trackedPaths.Count) `
        'Pristine Lean archive object-hash count differs from the pinned Git tree'
    for ($index = 0; $index -lt $trackedPaths.Count; $index++) {
        $relative = $trackedPaths[$index]
        Require-Condition ($archiveObjectHashes[$index] -eq $expectedArchiveObjects[$relative]) `
            "Pristine Lean archive blob mismatch: $relative"
    }
    Require-Condition (@($archivePaths | Where-Object { $_ -like '*.olean' }).Count -eq 0) `
        'Pristine Lean project archive unexpectedly contains an olean'
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $projectArchive).Hash.ToLowerInvariant() -ceq
        $script:LeanProjectArchiveSha256
    ) 'Pristine Lean project archive changed during extraction validation'
    $pristineSourceSha256 = [System.Collections.Generic.Dictionary[string,string]]::new(
        [System.StringComparer]::OrdinalIgnoreCase
    )
    foreach ($relative in $trackedPaths) {
        $pristineSourceFile = Get-ContainedPlainSingleLinkFile `
            -Root $cleanProject -Relative $relative `
            -Label "Pristine Lean project source $relative"
        $pristineSourceSha256.Add(
            $relative,
            (Get-FileHash -Algorithm SHA256 `
                -LiteralPath $pristineSourceFile).Hash.ToLowerInvariant()
        )
    }
    Write-Host "CHECK PRISTINE LEAN ARCHIVE OK files=$($trackedPaths.Count)"

    $leanBuild = Join-Path $RunRoot 'lean_build'
    New-Item -ItemType Directory -Path $leanBuild | Out-Null

    $lakeManifestPath = Join-Path $cleanProject 'lake-manifest.json'
    $lakeManifest = Get-Content -Raw -LiteralPath $lakeManifestPath | ConvertFrom-Json
    $pinnedPackageNames = @($lakeManifest.packages | ForEach-Object {
        Require-Condition ($_.type -eq 'git' -and $_.name -match '^[A-Za-z0-9_.-]+$') `
            "Unsupported Lake package record: $($_ | ConvertTo-Json -Compress)"
        $_.name
    })
    $repositoryPackageRoot = Join-Path $legacy '.lake\packages'
    $installedPackageNames = @(Get-ChildItem -LiteralPath $repositoryPackageRoot -Directory | ForEach-Object { $_.Name })
    $packageSetDifference = @(Compare-Object -ReferenceObject $pinnedPackageNames `
        -DifferenceObject $installedPackageNames -CaseSensitive)
    Require-Condition ($packageSetDifference.Count -eq 0) `
        "Installed Lake package directories differ from the pinned manifest: $($packageSetDifference -join ', ')"

    $cleanLake = Join-Path $cleanProject '.lake'
    $cleanPackageRoot = Join-Path $cleanLake 'packages'
    New-Item -ItemType Directory -Path $cleanLake | Out-Null
    New-Item -ItemType Directory -Path $cleanPackageRoot | Out-Null
    foreach ($packageName in $pinnedPackageNames) {
        $packageTarget = (Resolve-Path -LiteralPath (Join-Path $repositoryPackageRoot $packageName)).Path
        $packageLink = Join-Path $cleanPackageRoot $packageName
        New-Item -ItemType Junction -Path $packageLink -Target $packageTarget | Out-Null
    }

        Assert-LeanMemoryGate
        Invoke-Logged -Name 'lean_clean_baseline_build' -Command $lake `
            -Arguments @(
                '--rehash', '--offline', 'build'
            ) `
            -WorkingDirectory $cleanProject | Out-Null
        foreach ($relative in $trackedPaths) {
            $postBuildSourceFile = Get-ContainedPlainSingleLinkFile `
                -Root $cleanProject -Relative $relative `
                -Label "Post-build pristine Lean project source $relative"
            Require-Condition (
                (Get-FileHash -Algorithm SHA256 -LiteralPath $postBuildSourceFile).Hash.ToLowerInvariant() -ceq
                $pristineSourceSha256[$relative]
            ) "Pristine Lean project source changed during the clean build: $relative"
        }
        Require-Condition (
            (Get-FileHash -Algorithm SHA256 -LiteralPath $projectArchive).Hash.ToLowerInvariant() -ceq
            $script:LeanProjectArchiveSha256
        ) 'Pristine Lean project archive changed during the clean build'

        $baselineLeanLib = Join-Path $cleanProject '.lake\build_release_clean\lib\lean'
        Require-Condition (Test-Path -LiteralPath $baselineLeanLib -PathType Container) `
            "Baseline Lean library output is missing: $baselineLeanLib"
        $freshDossierOlean = Join-Path $baselineLeanLib `
            'LeechTrees\Expanded\FirstEdge\FirstEdgeDossier.olean'
        $freshDossierOlean = Get-ContainedPlainSingleLinkFile `
            -Root $cleanProject `
            -Relative '.lake/build_release_clean/lib/lean/LeechTrees/Expanded/FirstEdge/FirstEdgeDossier.olean' `
            -Label 'Fresh FirstEdgeDossier olean'
        $script:FreshBaselineLeanLib = $baselineLeanLib
        $script:FreshDossierOleanSha256 = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $freshDossierOlean).Hash.ToLowerInvariant()
        $leanPaths = @($baselineLeanLib, $leanBuild)
        foreach ($packageName in $pinnedPackageNames) {
            $candidate = Join-Path (Join-Path $cleanPackageRoot $packageName) '.lake\build\lib\lean'
            if (Test-Path -LiteralPath $candidate -PathType Container) {
                $leanPaths += $candidate
            }
        }
        $leanPaths += $ProofDir
        $env:LEAN_PATH = $leanPaths -join ';'
        Assert-LeanMemoryGate
        $boundarySource = Join-Path $ProofDir 'HybridEndToEndBoundary.lean'
        $boundaryOlean = Join-Path $leanBuild 'HybridEndToEndBoundary.olean'
        $auditOutput = Invoke-Logged -Name 'lean_hybrid_boundary' -Command $lean `
            -Arguments @(
                '-j', [string]$LeanElaborationThreads,
                $boundarySource, '-o', $boundaryOlean
            ) `
            -WorkingDirectory $ProofDir -RequireEmptyStderr
        foreach ($required in @(
            'LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier',
            'Leech18EndToEnd.no_order18_leech_of_all_rows'
        )) {
            Require-Condition $auditOutput.Contains($required) "Lean audit omitted $required"
        }
        $canonicalAuditOutput = $auditOutput -replace "`r`n", "`n" -replace "`r", "`n"
        $expectedAxiomReports = @{
            'LeechTrees.Foundation.FirstEdgeDossier.firstEdge_eightRowDossier' = 'propext, Classical.choice, Quot.sound'
            'Leech18EndToEnd.no_order18_leech_of_all_rows' = 'propext, Classical.choice, Quot.sound'
        }
        $axiomReports = @([regex]::Matches(
            $canonicalAuditOutput,
            "(?m)^'(?<declaration>[^'`n]+)' depends on axioms: \[(?<axioms>[^\]]*)\][ `t]*$"
        ))
        $axiomPhraseCount = [regex]::Matches($canonicalAuditOutput, 'depends on axioms:').Count
        Require-Condition (
            $axiomReports.Count -eq $expectedAxiomReports.Count -and
            $axiomPhraseCount -eq $axiomReports.Count
        ) "Lean audit did not contain exactly two canonical axiom reports"
        $seenAxiomReports = @{}
        foreach ($report in $axiomReports) {
            $declaration = $report.Groups['declaration'].Value
            $axioms = [regex]::Replace($report.Groups['axioms'].Value, '\s+', ' ').Trim()
            Require-Condition $expectedAxiomReports.ContainsKey($declaration) `
                "Lean audit reported axioms for an unexpected declaration: $declaration"
            Require-Condition (-not $seenAxiomReports.ContainsKey($declaration)) `
                "Lean audit repeated the axiom report for: $declaration"
            Require-Condition ($axioms -eq $expectedAxiomReports[$declaration]) `
                "Lean audit axiom list mismatch for ${declaration}: $axioms"
            $seenAxiomReports[$declaration] = $true
        }
        foreach ($forbidden in @('sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler')) {
            Require-Condition (-not $auditOutput.Contains($forbidden)) "Lean audit contains $forbidden"
        }
        Write-Host 'CHECK LEAN BOUNDARY AUDIT OK declarations=2'
    }
    finally {
        $env:LEAN_PATH = $oldLeanPath
        $env:LEAN_SRC_PATH = $oldLeanSrcPath
        $env:LEAN_SYSROOT = $oldLeanSysroot
        $env:LEAN = $oldLeanExecutable
        $env:LAKE_OVERRIDE_LEAN = $oldLakeOverrideLean
        $env:LEAN_NUM_THREADS = $oldLeanNumThreads
    }
}

try {
    Require-Condition (
        $null -eq (Get-Item -Force -LiteralPath $TranscriptPath `
            -ErrorAction SilentlyContinue)
    ) 'Outer transcript target already exists; refusing to overwrite it'
    Start-Transcript -LiteralPath $TranscriptPath -Force | Out-Null
    $TranscriptStarted = $true
    Write-Host 'LEECH18 HYBRID END-TO-END PROOF REPLAY'
    Write-Host "WORKSPACE_ROOT $WorkspaceRoot"
    Write-Host "RUN_LOGS $LogRoot"
    Test-PackageManifest
    $InitialPackageManifestSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath (Join-Path $ProofDir 'MANIFEST.sha256')).Hash.ToLowerInvariant()
    Require-PlainSingleLinkFile -Path $RecordPath -Label 'Proof record'
    $recordSha256BeforeCheck = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $RecordPath).Hash.ToLowerInvariant()

    $python = (Get-Command $PythonExecutable -ErrorAction Stop).Source
    $powershell = (Get-Command powershell.exe -ErrorAction Stop).Source
    $GitExecutablePath = (Get-Command git.exe -ErrorAction Stop).Source
    $TarExecutablePath = (Get-Command tar.exe -ErrorAction Stop).Source
    Require-PlainSingleLinkFile -Path $python -Label 'Python executable'
    $PythonExecutableSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $python).Hash.ToLowerInvariant()
    $PowerShellExecutableSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $powershell).Hash.ToLowerInvariant()
    $GitExecutableSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $GitExecutablePath).Hash.ToLowerInvariant()
    $TarExecutableSha256 = `
        (Get-FileHash -Algorithm SHA256 -LiteralPath $TarExecutablePath).Hash.ToLowerInvariant()
    foreach ($gitEnvironmentEntry in @(Get-ChildItem Env: | Where-Object { $_.Name -like 'GIT_*' })) {
        Remove-Item -LiteralPath ("Env:" + $gitEnvironmentEntry.Name)
    }
    $env:GIT_CONFIG_GLOBAL = 'NUL'
    $env:GIT_CONFIG_NOSYSTEM = '1'
    $env:GIT_OPTIONAL_LOCKS = '0'
    $env:GIT_TERMINAL_PROMPT = '0'
    $env:LEECH18_GIT_EXECUTABLE = $GitExecutablePath
    $env:PYTHONHOME = $null
    $env:PYTHONPATH = $null
    $env:PYTHONSTARTUP = $null
    $env:PYTHONUSERBASE = $null
    $env:PYTHONINSPECT = $null
    $env:PYTHONWARNINGS = $null
    $env:PYTHONBREAKPOINT = $null
    $env:PYTHONCASEOK = $null
    $env:PYTHONPLATLIBDIR = $null
    $env:PYTHONEXECUTABLE = $null
    $env:PYTHONSAFEPATH = $null
    $env:PYTHONNOUSERSITE = '1'
    $env:PYTHONDONTWRITEBYTECODE = '1'
    $env:PYTHONUTF8 = '1'
    $env:PYTHONHASHSEED = '0'

    Invoke-Logged -Name 'python_version' -Command $python `
        -Arguments @('-E', '-s', '-S', '-B', '--version') `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedNormalizedStdoutPattern '\APython 3\.[0-9]+\.[0-9]+[A-Za-z0-9.+-]*\z' `
        -RequireEmptyStderr | Out-Null

    Invoke-Logged -Name 'hybrid_record' -Command $python `
        -Arguments @('-E', '-s', '-S', '-B', (Join-Path $ProofDir 'verify_hybrid_record.py')) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedUniqueLastMarker 'LEECH18_HYBRID_RECORD_OK configurations=8 reported_node_visits=8565199014' `
        -RequireEmptyStderr | Out-Null

    # The Python checker rejects duplicate JSON keys and validates the exact
    # record schema before PowerShell is allowed to consume any record field.
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $RecordPath).Hash.ToLowerInvariant() -ceq
        $recordSha256BeforeCheck
    ) 'Proof record changed while the strict checker was running'
    $recordRaw = Get-Content -Raw -LiteralPath $RecordPath
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $RecordPath).Hash.ToLowerInvariant() -ceq
        $recordSha256BeforeCheck
    ) 'Proof record changed while PowerShell was reading it'
    $record = $recordRaw | ConvertFrom-Json
    $env:ELAN_TOOLCHAIN = $record.lean.toolchain

    $compactFreeze = Join-Path $WorkspaceRoot ($record.evidence.source_freeze.path -replace '/', '\')
    $compactSource = Split-Path -Parent $compactFreeze
    $expectedGlobal = Join-Path $WorkspaceRoot ($record.evidence.global_record.path -replace '/', '\')
    $priorThree = Join-Path $WorkspaceRoot ($record.evidence.prior_three_evidence.root -replace '/', '\')
    $fullSourcePlain = Join-Path $WorkspaceRoot ($record.evidence.source_freeze.full_replay_directory -replace '/', '\')
    $fullWorkspacePlain = Split-Path -Parent $fullSourcePlain
    Require-Condition (Test-Path -LiteralPath $fullWorkspacePlain -PathType Container) 'Full extracted Terminal5 workspace is missing'
    $fullWorkspace = Get-ExtendedWindowsPath -Path $fullWorkspacePlain
    $fullPlanJson = Join-Path $WorkspaceRoot ($record.evidence.terminal_plan.full_replay_path -replace '/', '\')
    $fullPlanPlain = Split-Path -Parent $fullPlanJson
    Require-Condition (
        (Resolve-Path -LiteralPath $fullSourcePlain).Path -eq
        (Resolve-Path -LiteralPath (Join-Path $fullWorkspacePlain 'source')).Path
    ) 'Recorded full source is not the workspace source directory'
    Require-Condition (
        (Resolve-Path -LiteralPath $fullPlanPlain).Path -eq
        (Resolve-Path -LiteralPath (Join-Path $fullWorkspacePlain 'plan\terminal5_plan_v1')).Path
    ) 'Recorded full plan is not the workspace terminal plan directory'
    $fullSource = "$fullWorkspace\source"
    $fullPlan = "$fullWorkspace\plan\terminal5_plan_v1"
    $fullRun = "$fullWorkspace\production_run\production_v1"

    Invoke-Logged -Name 'source_freeze' -Command $python `
        -Arguments @('-E', '-s', '-S', '-B', 'verify_g001_terminal5_source_freeze_v1.py', '--source-dir', '.') `
        -WorkingDirectory $compactSource `
        -ExpectedMarker 'G001_TERMINAL5_SOURCE_FREEZE_V1_OK files=28' `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.source_freeze `
        -RequireEmptyStderr | Out-Null

    Invoke-Logged -Name 'terminal5_source_tests' -Command $python `
        -Arguments @('-E', '-s', '-S', '-B', 'test_g001_terminal5_v1.py') `
        -WorkingDirectory $compactSource `
        -ExpectedMarker 'PASS test_g001_terminal5_v1 checks=47' `
        -ExpectedNormalizedStdoutPattern '\APASS test_g001_terminal5_v1 checks=47\z' `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.terminal5_source_tests `
        -RequireEmptyStderr | Out-Null

    $runtimeSourceOutput = Join-Path $RunRoot 'frozen_runtime_source'
    $runtimeSourceStdout = Invoke-Logged -Name 'frozen_runtime_source' -Command $python `
        -Arguments @(
            '-E', '-s', '-S', '-B', (Join-Path $ProofDir 'verify_frozen_runtime_source.py'),
            '--source-dir', $compactSource,
            '--output-dir', $runtimeSourceOutput,
            '--cxx', $Cxx
        ) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedMarker 'LEECH18_FROZEN_RUNTIME_SOURCE_OK solver_checks=45 checker_checks=11' `
        -ExpectedNormalizedStdoutPattern '\ALEECH18_FROZEN_RUNTIME_SOURCE_OK solver_checks=45 checker_checks=11 solver_sha256=[0-9a-f]{64} checker_sha256=[0-9a-f]{64}\z' `
        -RequireEmptyStderr
    $runtimeReportPath = Join-Path $runtimeSourceOutput `
        'runtime_source_validation.json'
    $runtimeManifestPath = Join-Path $runtimeSourceOutput `
        'runtime_source_validation.sha256'
    Require-PlainSingleLinkFile -Path $runtimeReportPath `
        -Label 'Frozen runtime-source report'
    Require-PlainSingleLinkFile -Path $runtimeManifestPath `
        -Label 'Frozen runtime-source output manifest'
    $runtimeManifestSha256BeforeValidation = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $runtimeManifestPath).Hash.ToLowerInvariant()
    $runtimeRootEntries = @(
        Get-ChildItem -Force -LiteralPath $runtimeSourceOutput |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    Require-Condition (
        ($runtimeRootEntries -join "`n") -ceq
        (@('bin', 'logs', 'runtime_source_validation.json',
            'runtime_source_validation.sha256') -join "`n")
    ) 'Frozen runtime-source output root exact-set mismatch'
    foreach ($runtimeDirectoryName in @('bin', 'logs')) {
        $runtimeDirectory = Join-Path $runtimeSourceOutput $runtimeDirectoryName
        $runtimeDirectoryInfo = Get-Item -Force -LiteralPath $runtimeDirectory
        Require-Condition (
            $runtimeDirectoryInfo.PSIsContainer -and
            ($runtimeDirectoryInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
        ) "Frozen runtime-source output directory is linked or not a directory: $runtimeDirectoryName"
    }
    $runtimeManifestRaw = Get-Content -Raw -LiteralPath $runtimeManifestPath
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $runtimeManifestPath).Hash.ToLowerInvariant() -ceq
        $runtimeManifestSha256BeforeValidation
    ) 'Frozen runtime-source output manifest changed while it was read'
    Require-Condition (
        $runtimeManifestRaw.Length -gt 0 -and
        $runtimeManifestRaw.EndsWith("`n") -and
        -not $runtimeManifestRaw.Contains("`r")
    ) 'Frozen runtime-source output manifest is not canonical LF text'
    $runtimeManifestEntries = [System.Collections.Generic.Dictionary[string,string]]::new(
        [System.StringComparer]::OrdinalIgnoreCase
    )
    $runtimeManifestOrder = [System.Collections.Generic.List[string]]::new()
    foreach ($line in @($runtimeManifestRaw.TrimEnd([char]10).Split("`n"))) {
        Require-Condition ($line -cmatch '^([0-9a-f]{64})  (.+)$') `
            "Malformed runtime-source manifest line: $line"
        $digest = $Matches[1]
        $relative = $Matches[2]
        Require-SafeReportRelativePath -Relative $relative `
            -Label 'runtime-source manifest'
        Require-Condition (-not $runtimeManifestEntries.ContainsKey($relative)) `
            "Duplicate/aliased runtime-source manifest path: $relative"
        $target = Get-ContainedPlainSingleLinkFile `
            -Root $runtimeSourceOutput -Relative $relative `
            -Label "Runtime-source output $relative"
        $actual = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $target).Hash.ToLowerInvariant()
        Require-Condition ($actual -ceq $digest) `
            "Runtime-source output digest mismatch: $relative"
        $runtimeManifestEntries.Add($relative, $digest)
        $runtimeManifestOrder.Add($relative)
    }
    $runtimeTargets = @(
        'g001_remaining_witness_solver',
        'check_g001_leech_witness',
        'test_g001_remaining_witness_solver'
    )
    $runtimeExpectedFiles = @(
        'runtime_source_validation.json'
        foreach ($targetName in $runtimeTargets) { "bin/$targetName.exe" }
        'logs/compiler_version.stdout.txt'
        'logs/compiler_version.stderr.txt'
        foreach ($targetName in $runtimeTargets) {
            "logs/compile_$targetName.stdout.txt"
            "logs/compile_$targetName.stderr.txt"
        }
        'logs/witness_regression.stdout.txt'
        'logs/witness_regression.stderr.txt'
        'logs/checker_self_test.stdout.txt'
        'logs/checker_self_test.stderr.txt'
    )
    $runtimeExpectedBinEntries = @(
        $runtimeExpectedFiles |
            Where-Object { $_.StartsWith('bin/', [System.StringComparison]::Ordinal) } |
            ForEach-Object { $_.Substring(4) } |
            Sort-Object
    )
    $runtimeExpectedLogEntries = @(
        $runtimeExpectedFiles |
            Where-Object { $_.StartsWith('logs/', [System.StringComparison]::Ordinal) } |
            ForEach-Object { $_.Substring(5) } |
            Sort-Object
    )
    foreach ($runtimeDirectoryContract in @(
        @{ Name = 'bin'; Expected = $runtimeExpectedBinEntries },
        @{ Name = 'logs'; Expected = $runtimeExpectedLogEntries }
    )) {
        $runtimeObservedChildren = @(
            Get-ChildItem -Force -LiteralPath `
                (Join-Path $runtimeSourceOutput $runtimeDirectoryContract.Name) |
                ForEach-Object { $_.Name } |
                Sort-Object
        )
        Require-Condition (
            ($runtimeObservedChildren -join "`n") -ceq
            (@($runtimeDirectoryContract.Expected) -join "`n")
        ) "Frozen runtime-source $($runtimeDirectoryContract.Name) exact-set mismatch"
    }
    Require-Condition (
        (@($runtimeManifestEntries.Keys | Sort-Object) -join "`n") -ceq
        (@($runtimeExpectedFiles | Sort-Object) -join "`n")
    ) 'Frozen runtime-source manifest exact-set mismatch'
    Require-Condition (
        (@($runtimeManifestOrder) -join "`n") -ceq
        (@($runtimeExpectedFiles | Sort-Object) -join "`n")
    ) 'Frozen runtime-source manifest is not sorted by path'

    $runtimeReport = Get-Content -Raw -LiteralPath $runtimeReportPath |
        ConvertFrom-Json
    $runtimeReportFields = @($runtimeReport.PSObject.Properties.Name | Sort-Object)
    $expectedRuntimeReportFields = @(
        'binaries',
        'binaries_rehashed_after_tests',
        'compile_flags',
        'compiler',
        'compiler_dynamic_environment_sanitized',
        'compiler_include_environment_sanitized',
        'compiler_rehashed_after_tests',
        'output_tree_exact',
        'pinned_source_files',
        'production_binary_identity_claimed',
        'sanitized_environment_variables',
        'schema',
        'source_dir',
        'source_hashes',
        'source_rehashed_after_tests',
        'tests'
    )
    Require-Condition (
        ($runtimeReportFields -join "`n") -ceq
        ($expectedRuntimeReportFields -join "`n")
    ) 'Frozen runtime-source report field set mismatch'
    Require-Condition (
        $runtimeReport.schema -eq 'LEECH18_FROZEN_RUNTIME_SOURCE_VALIDATION_V1' -and
        $runtimeReport.pinned_source_files -eq 8 -and
        (@($runtimeReport.compile_flags) -join "`n") -ceq
            (@('-O2', '-std=c++20', '-Wall', '-Wextra', '-Wpedantic', '-Werror') -join "`n") -and
        $runtimeReport.tests.solver_regression_checks -eq 45 -and
        $runtimeReport.tests.independent_checker_self_test_checks -eq 11 -and
        $runtimeReport.compiler_include_environment_sanitized -eq $true -and
        $runtimeReport.compiler_dynamic_environment_sanitized -eq $true -and
        $runtimeReport.compiler_rehashed_after_tests -eq $true -and
        $runtimeReport.source_rehashed_after_tests -eq $true -and
        $runtimeReport.binaries_rehashed_after_tests -eq $true -and
        $runtimeReport.output_tree_exact -eq $true -and
        $runtimeReport.production_binary_identity_claimed -eq $false -and
        @($runtimeReport.source_hashes.PSObject.Properties).Count -eq 8 -and
        @($runtimeReport.binaries.PSObject.Properties).Count -eq 3
    ) 'Frozen runtime-source report contract mismatch'
    $runtimeTestFields = @($runtimeReport.tests.PSObject.Properties.Name | Sort-Object)
    Require-Condition (
        ($runtimeTestFields -join "`n") -ceq
        (@('independent_checker_self_test_checks', 'solver_regression_checks') -join "`n")
    ) 'Frozen runtime-source test field set mismatch'

    $runtimeExpectedSourceNames = @(
        'a2_multi_edge_exact_cover.hpp',
        'a2_multi_edge_exact_cover_optimized.hpp',
        'a2_multi_edge_stronger_relaxation.hpp',
        'check_g001_leech_witness.cpp',
        'g001_remaining_witness_solver.cpp',
        'multi_edge_parity_coherence.hpp',
        'order18_topology_free_search.cpp',
        'test_g001_remaining_witness_solver.cpp'
    )
    $runtimeSourceNames = @($runtimeReport.source_hashes.PSObject.Properties.Name | Sort-Object)
    Require-Condition (
        ($runtimeSourceNames -join "`n") -ceq
        ($runtimeExpectedSourceNames -join "`n")
    ) 'Frozen runtime-source report source exact-set mismatch'
    foreach ($runtimeSourceName in $runtimeExpectedSourceNames) {
        $runtimeSourceDigest = [string](
            $runtimeReport.source_hashes.PSObject.Properties[$runtimeSourceName].Value
        )
        Require-Condition ($runtimeSourceDigest -cmatch '^[0-9a-f]{64}$') `
            "Malformed frozen runtime-source digest: $runtimeSourceName"
        $runtimeSourceFile = Get-ContainedPlainSingleLinkFile `
            -Root $compactSource -Relative $runtimeSourceName `
            -Label "Frozen runtime source $runtimeSourceName"
        Require-Condition (
            (Get-FileHash -Algorithm SHA256 -LiteralPath $runtimeSourceFile).Hash.ToLowerInvariant() -ceq
            $runtimeSourceDigest
        ) "Frozen runtime-source report digest mismatch: $runtimeSourceName"
    }

    $runtimeExpectedSanitizedVariables = @(
        'C_INCLUDE_PATH', 'COMPILER_PATH', 'CPATH', 'CPLUS_INCLUDE_PATH',
        'DEPENDENCIES_OUTPUT', 'DYLD_FALLBACK_FRAMEWORK_PATH',
        'DYLD_FALLBACK_LIBRARY_PATH', 'DYLD_FRAMEWORK_PATH',
        'DYLD_INSERT_LIBRARIES', 'DYLD_LIBRARY_PATH', 'GCC_EXEC_PREFIX',
        'GCC_COMPARE_DEBUG', 'GCC_COMPARE_DEBUG_ORIGINAL', 'GXX_INCLUDE_PATH',
        'INCLUDE', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LIB', 'LIBPATH',
        'LIBRARY_PATH', 'SUNPRO_DEPENDENCIES'
    )
    Require-Condition (
        (@($runtimeReport.sanitized_environment_variables) -join "`n") -ceq
        ($runtimeExpectedSanitizedVariables -join "`n")
    ) 'Frozen runtime-source sanitized-environment inventory mismatch'

    $runtimeBinaryNames = @($runtimeReport.binaries.PSObject.Properties.Name | Sort-Object)
    Require-Condition (
        ($runtimeBinaryNames -join "`n") -ceq
        (@($runtimeTargets | Sort-Object) -join "`n")
    ) 'Frozen runtime-source binary exact-set mismatch'
    foreach ($runtimeTarget in $runtimeTargets) {
        $runtimeBinaryBinding = `
            $runtimeReport.binaries.PSObject.Properties[$runtimeTarget].Value
        $runtimeBinaryFields = @($runtimeBinaryBinding.PSObject.Properties.Name | Sort-Object)
        Require-Condition (($runtimeBinaryFields -join ',') -ceq 'path,sha256') `
            "Malformed frozen runtime-source binary binding: $runtimeTarget"
        $runtimeBinaryRelative = "bin/$runtimeTarget.exe"
        $runtimeBinaryDigest = [string]$runtimeBinaryBinding.sha256
        Require-Condition (
            [string]$runtimeBinaryBinding.path -ceq $runtimeBinaryRelative -and
            $runtimeBinaryDigest -cmatch '^[0-9a-f]{64}$' -and
            $runtimeManifestEntries[$runtimeBinaryRelative] -ceq $runtimeBinaryDigest
        ) "Frozen runtime-source binary binding mismatch: $runtimeTarget"
    }
    $runtimeSourceMarker = [regex]::Match(
        ($runtimeSourceStdout -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10),
        '\ALEECH18_FROZEN_RUNTIME_SOURCE_OK solver_checks=45 checker_checks=11 ' +
        'solver_sha256=(?<solver>[0-9a-f]{64}) checker_sha256=(?<checker>[0-9a-f]{64})\z'
    )
    $runtimeSolverBinding = $runtimeReport.binaries.PSObject.Properties[
        'g001_remaining_witness_solver'
    ].Value
    $runtimeCheckerBinding = $runtimeReport.binaries.PSObject.Properties[
        'check_g001_leech_witness'
    ].Value
    Require-Condition (
        $runtimeSourceMarker.Success -and
        $runtimeSourceMarker.Groups['solver'].Value -ceq
            ([string]$runtimeSolverBinding.sha256) -and
        $runtimeSourceMarker.Groups['checker'].Value -ceq
            ([string]$runtimeCheckerBinding.sha256)
    ) 'Frozen runtime-source terminal marker does not bind the reported binaries'

    $runtimeCompilerFields = @($runtimeReport.compiler.PSObject.Properties.Name | Sort-Object)
    Require-Condition (
        ($runtimeCompilerFields -join ',') -ceq
        'path,sha256,version_stderr_sha256,version_stdout_sha256'
    ) 'Frozen runtime-source compiler field set mismatch'
    foreach ($runtimeCompilerDigestName in @(
        'sha256', 'version_stdout_sha256', 'version_stderr_sha256'
    )) {
        Require-Condition (
            [string]$runtimeReport.compiler.$runtimeCompilerDigestName -cmatch '^[0-9a-f]{64}$'
        ) "Malformed frozen runtime-source compiler digest: $runtimeCompilerDigestName"
    }
    $runtimeCompilerPath = [string]$runtimeReport.compiler.path
    Require-Condition ([System.IO.Path]::IsPathRooted($runtimeCompilerPath)) `
        'Frozen runtime-source compiler path is not absolute'
    Require-PlainSingleLinkFile -Path $runtimeCompilerPath `
        -Label 'Frozen runtime-source compiler executable'
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $runtimeCompilerPath).Hash.ToLowerInvariant() -ceq
        [string]$runtimeReport.compiler.sha256
    ) 'Frozen runtime-source compiler executable changed after the inner verifier'
    foreach ($runtimeCompilerStream in @('stdout', 'stderr')) {
        $runtimeCompilerLogRelative = "logs/compiler_version.$runtimeCompilerStream.txt"
        $runtimeCompilerDigestProperty = "version_${runtimeCompilerStream}_sha256"
        $runtimeCompilerReportDigest = [string](
            $runtimeReport.compiler.PSObject.Properties[$runtimeCompilerDigestProperty].Value
        )
        Require-Condition (
            $runtimeManifestEntries[$runtimeCompilerLogRelative] -ceq
            $runtimeCompilerReportDigest
        ) "Frozen runtime-source compiler-version $runtimeCompilerStream binding mismatch"
    }
    $reportedRuntimeSourceDirectory = [System.IO.Path]::GetFullPath(
        [string]$runtimeReport.source_dir
    ).TrimEnd('\')
    Require-Condition (
        $reportedRuntimeSourceDirectory.Equals(
            [System.IO.Path]::GetFullPath($compactSource).TrimEnd('\'),
            [System.StringComparison]::OrdinalIgnoreCase
        )
    ) 'Frozen runtime-source report names a different source directory'
    $finalRuntimeRootEntries = @(
        Get-ChildItem -Force -LiteralPath $runtimeSourceOutput |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    Require-Condition (
        ($finalRuntimeRootEntries -join "`n") -ceq
        ($runtimeRootEntries -join "`n")
    ) 'Frozen runtime-source root changed during outer validation'
    foreach ($runtimeDirectoryContract in @(
        @{ Name = 'bin'; Expected = $runtimeExpectedBinEntries },
        @{ Name = 'logs'; Expected = $runtimeExpectedLogEntries }
    )) {
        $finalRuntimeChildren = @(
            Get-ChildItem -Force -LiteralPath `
                (Join-Path $runtimeSourceOutput $runtimeDirectoryContract.Name) |
                ForEach-Object { $_.Name } |
                Sort-Object
        )
        Require-Condition (
            ($finalRuntimeChildren -join "`n") -ceq
            (@($runtimeDirectoryContract.Expected) -join "`n")
        ) "Frozen runtime-source $($runtimeDirectoryContract.Name) changed during outer validation"
    }
    foreach ($runtimeManifestEntry in $runtimeManifestEntries.GetEnumerator()) {
        $runtimeFinalFile = Get-ContainedPlainSingleLinkFile `
            -Root $runtimeSourceOutput -Relative $runtimeManifestEntry.Key `
            -Label "Final runtime-source output $($runtimeManifestEntry.Key)"
        Require-Condition (
            (Get-FileHash -Algorithm SHA256 -LiteralPath $runtimeFinalFile).Hash.ToLowerInvariant() -ceq
            $runtimeManifestEntry.Value
        ) "Frozen runtime-source output changed during outer validation: $($runtimeManifestEntry.Key)"
    }
    $RuntimeSourceReportSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $runtimeReportPath).Hash.ToLowerInvariant()
    $RuntimeSourceManifestSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $runtimeManifestPath).Hash.ToLowerInvariant()
    Require-Condition (
        $RuntimeSourceManifestSha256 -ceq $runtimeManifestSha256BeforeValidation
    ) 'Frozen runtime-source output manifest changed during outer validation'
    Require-Condition (
        $runtimeManifestEntries['runtime_source_validation.json'] -ceq
        $RuntimeSourceReportSha256
    ) 'Frozen runtime-source report is not bound by its output manifest'

    $planRegeneration = $record.evidence.terminal_plan.regeneration
    $regeneratedPlan = Join-Path $RunRoot 'regenerated_terminal_plan'
    $terminalRuntime = Get-ExtendedWindowsPath -Path `
        (Join-Path $WorkspaceRoot ($planRegeneration.runtime_directory -replace '/', '\'))
    $c157Archive = Get-ExtendedWindowsPath -Path `
        (Join-Path $WorkspaceRoot ($planRegeneration.c157_archive_path -replace '/', '\'))
    $c157Package = Get-ExtendedWindowsPath -Path `
        (Join-Path $WorkspaceRoot ($planRegeneration.c157_package_path -replace '/', '\'))
    $config4Archive = Get-ExtendedWindowsPath -Path `
        (Join-Path $WorkspaceRoot ($planRegeneration.config4_archive_path -replace '/', '\'))
    $config4Package = Get-ExtendedWindowsPath -Path `
        (Join-Path $WorkspaceRoot ($planRegeneration.config4_package_path -replace '/', '\'))
    $planBuildMarker = `
        'G001_TERMINAL5_PLAN_V1_OK records=39030 search=39000 zero=30 bundles=192 sha256=' + `
        $record.evidence.terminal_plan.sha256
    Invoke-Logged -Name 'terminal_plan_regeneration_build' -Command $python `
        -Arguments @(
            '-E', '-s', '-S', '-B', (Join-Path $fullSourcePlain $planRegeneration.builder_source_relative_path),
            '--c157-archive', $c157Archive,
            '--c157-package', $c157Package,
            '--config4-archive', $config4Archive,
            '--config4-package', $config4Package,
            '--workspace', $fullWorkspace,
            '--source-dir', $fullSource,
            '--runtime-dir', $terminalRuntime,
            '--output', $regeneratedPlan,
            '--plan-id', $planRegeneration.plan_id
        ) `
        -WorkingDirectory $fullSourcePlain `
        -ExpectedMarker $planBuildMarker `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.terminal_plan_regeneration_build `
        -RequireEmptyStderr | Out-Null

    $planCompareMarker = `
        'LEECH18_TERMINAL_PLAN_REGENERATION_OK files=195 plan_sha256=' + `
        $record.evidence.terminal_plan.sha256
    Invoke-Logged -Name 'terminal_plan_regeneration_compare' -Command $python `
        -Arguments @(
            '-E', '-s', '-S', '-B', (Join-Path $ProofDir 'verify_terminal_plan_regeneration.py'),
            '--frozen', $fullPlan,
            '--regenerated', $regeneratedPlan,
            '--plan-sha256', $record.evidence.terminal_plan.sha256,
            '--manifest-sha256', $record.evidence.terminal_plan.full_manifest_sha256,
            '--receipt-sha256', $record.evidence.terminal_plan.full_receipt_sha256
        ) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedMarker $planCompareMarker `
        -ExpectedNormalizedStdoutPattern ('\A' + [regex]::Escape($planCompareMarker) + '\z') `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.terminal_plan_regeneration_compare `
        -RequireEmptyStderr | Out-Null
    $RegeneratedPlanSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath (Join-Path $regeneratedPlan 'terminal_plan_v1.json')).Hash.ToLowerInvariant()
    $RegeneratedPlanManifestSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath (Join-Path $regeneratedPlan 'plan_artifacts.sha256')).Hash.ToLowerInvariant()
    $RegeneratedPlanReceiptSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath (Join-Path $regeneratedPlan 'plan_receipt.json')).Hash.ToLowerInvariant()
    Require-Condition ($RegeneratedPlanSha256 -eq $record.evidence.terminal_plan.sha256) `
        'Regenerated terminal-plan hash changed after comparison'
    Require-Condition ($RegeneratedPlanManifestSha256 -eq $record.evidence.terminal_plan.full_manifest_sha256) `
        'Regenerated terminal-plan manifest hash changed after comparison'
    Require-Condition ($RegeneratedPlanReceiptSha256 -eq $record.evidence.terminal_plan.full_receipt_sha256) `
        'Regenerated terminal-plan receipt hash changed after comparison'

    Build-LeanBoundary -Record $record

    $semantic = $record.evidence.semantic_bridge
    Require-Condition ($semantic.status -eq 'PASS') `
        'Semantic bridge has not completed its required fresh-baseline Lean replay'
    Require-Condition ($null -ne $FreshBaselineLeanLib) `
        'Fresh baseline Lean library was not retained for the semantic bridge'
    $semanticWrapper = Join-Path $WorkspaceRoot ($semantic.wrapper_path -replace '/', '\')
    $semanticRunRoot = Join-Path $RunRoot 'semantic_bridge'
    $semanticMarker = $semantic.expected_marker
    $semanticOutput = Invoke-Logged -Name 'semantic_bridge' -Command $powershell `
        -Arguments @(
            '-NoProfile', '-ExecutionPolicy', 'Bypass',
            '-File', $semanticWrapper,
            '-BaselineLeanLib', $FreshBaselineLeanLib,
            '-RunRoot', $semanticRunRoot
        ) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedMarker $semanticMarker `
        -RequireEmptyStderr
    $semanticNormalized = `
        ($semanticOutput -replace "`r`n", "`n" -replace "`r", "`n").TrimEnd([char]10)
    $semanticLines = @($semanticNormalized.Split("`n"))
    Require-Condition ($semanticLines[-1] -ceq $semanticMarker) `
        'Semantic bridge replay marker was not the exact last stdout line'
    Require-Condition (
        @($semanticLines | Where-Object { $_ -ceq $semanticMarker }).Count -eq 1
    ) 'Semantic bridge replay marker was not unique'
    $semanticStaticMarker =
        'LEECH18_SEMANTIC_BRIDGE_STATIC_OK rows=8 lean_elaboration=NOT_CHECKED'
    Require-Condition (
        @($semanticLines | Where-Object { $_ -ceq $semanticStaticMarker }).Count -eq 1
    ) 'Semantic bridge preliminary static-check marker was not unique'
    Require-Condition ($semanticNormalized.Contains(
        "CHECK BASELINE DOSSIER OLEAN sha256=$FreshDossierOleanSha256")) `
        'Semantic bridge did not bind the fresh dossier olean hash'

    $semanticResultPath = Join-Path $semanticRunRoot 'RUN_RESULT.json'
    $semanticResultSidecar = Join-Path $semanticRunRoot 'RUN_RESULT.sha256'
    Require-Condition (Test-Path -LiteralPath $semanticResultPath -PathType Leaf) `
        'Semantic bridge deterministic run result is missing'
    Require-Condition (Test-Path -LiteralPath $semanticResultSidecar -PathType Leaf) `
        'Semantic bridge deterministic run-result sidecar is missing'
    Require-PlainSingleLinkFile -Path $semanticResultPath `
        -Label 'Semantic bridge deterministic run result'
    Require-PlainSingleLinkFile -Path $semanticResultSidecar `
        -Label 'Semantic bridge deterministic run-result sidecar'
    $SemanticBridgeRunResultSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $semanticResultPath).Hash.ToLowerInvariant()
    $SemanticBridgeRunResultSidecarSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $semanticResultSidecar).Hash.ToLowerInvariant()
    Require-Condition (
        $SemanticBridgeRunResultSha256 -eq $semantic.run_result_sha256
    ) 'Semantic bridge deterministic run-result hash mismatch'
    Require-Condition (
        $SemanticBridgeRunResultSidecarSha256 -eq $semantic.run_result_sidecar_sha256
    ) 'Semantic bridge deterministic run-result sidecar hash mismatch'
    $semanticSidecarText = Get-Content -Raw -LiteralPath $semanticResultSidecar
    Require-Condition (
        $semanticSidecarText -ceq "$SemanticBridgeRunResultSha256  RUN_RESULT.json`n"
    ) 'Semantic bridge run-result sidecar content mismatch'
    $semanticMetadataPattern = '(?m)^RUN_RESULT_JSON ' +
        [regex]::Escape($semanticResultPath) + ' sha256=' +
        $SemanticBridgeRunResultSha256 + ' sidecar=' +
        [regex]::Escape($semanticResultSidecar) + '$'
    Require-Condition (
        [regex]::Matches($semanticNormalized, $semanticMetadataPattern).Count -eq 1
    ) 'Semantic bridge stdout did not bind its deterministic run result exactly once'

    $semanticResultRaw = Get-Content -Raw -LiteralPath $semanticResultPath
    foreach ($forbiddenSemanticRoot in @(
        $RunRoot, $WorkspaceRoot, $FreshBaselineLeanLib,
        $env:USERPROFILE, $env:HOME, $env:LOCALAPPDATA, $env:APPDATA,
        $env:TEMP, $env:TMP
    )) {
        if (-not [string]::IsNullOrWhiteSpace($forbiddenSemanticRoot)) {
            Require-Condition (
                $semanticResultRaw.IndexOf(
                    [string]$forbiddenSemanticRoot,
                    [System.StringComparison]::OrdinalIgnoreCase
                ) -lt 0
            ) 'Semantic bridge deterministic run result contains a host-root path'
        }
    }
    foreach ($semanticHostPathPattern in @(
        '(?i)(?:\\\\\?\\)?[a-z]:[\\/]',
        '(?i)(?:^|[\s=''\"])/(?:home|users|private|tmp)/',
        '(?i)\\\\[^\\\s]+\\[^\\\s]+'
    )) {
        Require-Condition (-not [regex]::IsMatch(
            $semanticResultRaw, $semanticHostPathPattern
        )) 'Semantic bridge deterministic run result contains an absolute host path'
    }
    $semanticResult = $semanticResultRaw | ConvertFrom-Json
    $expectedSemanticResultFields = @(
        'artifacts', 'axiom_allowlist', 'axiom_audit_declarations',
        'baseline_dossier_olean_sha256', 'baseline_mode', 'bridge_sources',
        'full_checker_stdout_sha256', 'lean_elaboration_threads',
        'lean_emitter_stdout_sha256', 'lean_source_commit', 'lean_toolchain',
        'logs', 'pinned_inputs',
        'record_sha256', 'schema', 'status', 'terminal_marker'
    )
    $actualSemanticResultFields = @(
        $semanticResult.PSObject.Properties.Name | Sort-Object
    )
    Require-Condition (
        ($actualSemanticResultFields -join "`n") -ceq
        ($expectedSemanticResultFields -join "`n")
    ) 'Semantic bridge deterministic run-result field set mismatch'
    Require-Condition (
        $semanticResult.schema -eq $semantic.run_result_schema -and
        $semanticResult.status -eq 'PASS' -and
        $semanticResult.terminal_marker -ceq $semanticMarker -and
        $semanticResult.baseline_mode -eq 'explicit_fresh' -and
        $semanticResult.baseline_dossier_olean_sha256 -eq $FreshDossierOleanSha256 -and
        (($semanticResult.lean_elaboration_threads -is [int]) -or
            ($semanticResult.lean_elaboration_threads -is [long])) -and
        $semanticResult.lean_elaboration_threads -eq $LeanElaborationThreads -and
        $semanticResult.lean_toolchain -eq $record.lean.toolchain -and
        $semanticResult.lean_source_commit -eq $record.lean.commit -and
        $semanticResult.record_sha256 -eq $semantic.record_sha256
    ) 'Semantic bridge deterministic run-result header mismatch'
    Require-Condition (
        (@($semanticResult.axiom_allowlist) -join ',') -ceq
        'Classical.choice,Quot.sound,propext'
    ) 'Semantic bridge canonical axiom allowlist mismatch'
    $expectedSemanticAxiomDeclarations = @(
        'Leech18SemanticBridge.rowDescriptors_all_wellFormed',
        'Leech18SemanticBridge.eightRowDossier_implies_some_realized_core',
        'Leech18SemanticBridge.isLeech_implies_some_realized_seed_descriptor',
        'Leech18SemanticBridge.adjacentMeetsTwoRow_implies_a2_production_split'
    )
    Require-Condition (
        (@($semanticResult.axiom_audit_declarations) -join "`n") -ceq
        ($expectedSemanticAxiomDeclarations -join "`n")
    ) 'Semantic bridge canonical axiom-declaration list mismatch'
    $expectedSemanticBridgeSources = @(
        'LeanRowSemanticBridge.lean',
        'README.md',
        'SEMANTIC_BRIDGE_RECORD.json',
        'verify_semantic_bridge.py',
        'verify_semantic_bridge.ps1',
        'SemanticBridge/A2Split.lean',
        'SemanticBridge/AdjacentRows.lean',
        'SemanticBridge/Aggregate.lean',
        'SemanticBridge/DescriptorData.lean',
        'SemanticBridge/DescriptorWellFormed.lean',
        'SemanticBridge/DisjointRows.lean',
        'SemanticBridge/RowCore.lean'
    )
    $semanticBridgeSourceRoot = Join-Path $ProofDir 'semantic_bridge'
    $null = Test-ExactPathHashInventory `
        -Records @($semanticResult.bridge_sources) `
        -ExpectedPaths $expectedSemanticBridgeSources `
        -Root $semanticBridgeSourceRoot `
        -Label 'Semantic bridge source' `
        -Rehash

    $expectedSemanticArtifacts = @(
        'lean_build/LeanRowSemanticBridge.olean',
        'lean_build/SemanticBridge/A2Split.olean',
        'lean_build/SemanticBridge/AdjacentRows.olean',
        'lean_build/SemanticBridge/Aggregate.olean',
        'lean_build/SemanticBridge/DescriptorData.olean',
        'lean_build/SemanticBridge/DescriptorWellFormed.olean',
        'lean_build/SemanticBridge/DisjointRows.olean',
        'lean_build/SemanticBridge/RowCore.olean'
    )
    $null = Test-ExactPathHashInventory `
        -Records @($semanticResult.artifacts) `
        -ExpectedPaths $expectedSemanticArtifacts `
        -Root $semanticRunRoot `
        -Label 'Semantic bridge artifact' `
        -Rehash

    $semanticLogStems = @(
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
    )
    $expectedSemanticLogs = @(
        foreach ($stem in $semanticLogStems) {
            "logs/$stem.stdout.txt"
            "logs/$stem.stderr.txt"
        }
    )
    $semanticLogHashes = Test-ExactPathHashInventory `
        -Records @($semanticResult.logs) `
        -ExpectedPaths $expectedSemanticLogs `
        -Root $semanticRunRoot `
        -Label 'Semantic bridge log' `
        -Rehash
    Require-Condition (
        $semanticLogHashes['logs/lean_semantic_bridge.stdout.txt'] -eq
            $semanticResult.lean_emitter_stdout_sha256 -and
        $semanticLogHashes['logs/full_semantic_bridge.stdout.txt'] -eq
            $semanticResult.full_checker_stdout_sha256
    ) 'Semantic bridge named stdout bindings mismatch'

    $semanticSourceRecord = Get-Content -Raw -LiteralPath `
        (Join-Path $semanticBridgeSourceRoot 'SEMANTIC_BRIDGE_RECORD.json') |
        ConvertFrom-Json
    $expectedSemanticInputs = [System.Collections.Generic.Dictionary[string,object]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($property in $semanticSourceRecord.inputs.PSObject.Properties) {
        $expectedSemanticInputs.Add($property.Name, $property.Value)
    }
    $expectedSemanticInputRoles = @(
        'a2_production_source',
        'authoritative_dossier_olean',
        'authoritative_lean_dossier',
        'configuration2_certificate',
        'configuration3_certificate',
        'configuration3_partition_ledger',
        'configuration8_certificate',
        'final_five_solver',
        'final_five_source_freeze',
        'lake_manifest',
        'lakefile',
        'lean_toolchain',
        'row1_production_snapshot',
        'row7_production_snapshot',
        'solver_core'
    )
    Require-Condition (
        (@($expectedSemanticInputs.Keys | Sort-Object) -join "`n") -ceq
        (@($expectedSemanticInputRoles | Sort-Object) -join "`n")
    ) 'Semantic bridge source record input-role exact set mismatch'
    $observedSemanticInputs = [System.Collections.Generic.Dictionary[string,bool]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($item in @($semanticResult.pinned_inputs)) {
        $fields = @($item.PSObject.Properties.Name | Sort-Object)
        Require-Condition (($fields -join ',') -ceq 'path,role,sha256') `
            'Malformed semantic bridge pinned-input item'
        $role = [string]$item.role
        $path = [string]$item.path
        $digest = [string]$item.sha256
        Require-Condition (
            $role.Length -gt 0 -and
            $expectedSemanticInputs.ContainsKey($role) -and
            -not $observedSemanticInputs.ContainsKey($role)
        ) "Unexpected or duplicate semantic bridge input role: $role"
        Require-SafeReportRelativePath -Relative $path `
            -Label "Semantic bridge pinned input $role"
        Require-Condition ($digest -cmatch '^[0-9a-f]{64}$') `
            "Malformed semantic bridge input digest: $role"
        $expectedInput = $expectedSemanticInputs[$role]
        Require-Condition (
            $path -ceq [string]$expectedInput.path -and
            $digest -ceq ([string]$expectedInput.sha256).ToLowerInvariant()
        ) "Semantic bridge input differs from source record: $role"
        if ($role -cne 'authoritative_dossier_olean') {
            $semanticInputFile = Get-ContainedPlainSingleLinkFile `
                -Root $WorkspaceRoot -Relative $path `
                -Label "Semantic bridge pinned input $role"
            $semanticInputActual = (Get-FileHash -Algorithm SHA256 `
                -LiteralPath $semanticInputFile).Hash.ToLowerInvariant()
            Require-Condition ($semanticInputActual -ceq $digest) `
                "Semantic bridge pinned-input file digest mismatch: $role"
        }
        $observedSemanticInputs.Add($role, $true)
    }
    Require-Condition ($observedSemanticInputs.Count -eq $expectedSemanticInputs.Count) `
        'Semantic bridge pinned-input exact set mismatch'
    Require-Condition (
        (Get-FileHash -Algorithm SHA256 -LiteralPath $semanticResultPath).Hash.ToLowerInvariant() -eq
        $SemanticBridgeRunResultSha256 -and
        (Get-FileHash -Algorithm SHA256 -LiteralPath $semanticResultSidecar).Hash.ToLowerInvariant() -eq
        $SemanticBridgeRunResultSidecarSha256
    ) 'Semantic bridge result or sidecar changed during outer validation'
    $semanticRunRootEntries = @(
        Get-ChildItem -Force -LiteralPath $semanticRunRoot |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    Require-Condition (
        ($semanticRunRootEntries -join "`n") -ceq
        (@('lean_build', 'logs', 'RUN_RESULT.json', 'RUN_RESULT.sha256') -join "`n")
    ) 'Semantic bridge outer run-root exact-set mismatch'
    $semanticBuildRoot = Join-Path $semanticRunRoot 'lean_build'
    $semanticBuildEntries = @(
        Get-ChildItem -Force -LiteralPath $semanticBuildRoot |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    Require-Condition (
        ($semanticBuildEntries -join "`n") -ceq
        (@('LeanRowSemanticBridge.olean', 'SemanticBridge') -join "`n")
    ) 'Semantic bridge outer lean-build root exact-set mismatch'
    $semanticModuleRoot = Join-Path $semanticBuildRoot 'SemanticBridge'
    $semanticModuleEntries = @(
        Get-ChildItem -Force -LiteralPath $semanticModuleRoot |
            ForEach-Object { $_.Name } |
            Sort-Object
    )
    $expectedSemanticModuleEntries = @(
        'A2Split.olean',
        'AdjacentRows.olean',
        'Aggregate.olean',
        'DescriptorData.olean',
        'DescriptorWellFormed.olean',
        'DisjointRows.olean',
        'RowCore.olean'
    )
    Require-Condition (
        ($semanticModuleEntries -join "`n") -ceq
        ($expectedSemanticModuleEntries -join "`n")
    ) 'Semantic bridge outer module-build exact-set mismatch'
    foreach ($semanticOutputDirectory in @(
        $semanticRunRoot, $semanticBuildRoot, $semanticModuleRoot,
        (Join-Path $semanticRunRoot 'logs')
    )) {
        $semanticOutputDirectoryInfo = Get-Item -Force -LiteralPath $semanticOutputDirectory
        Require-Condition (
            $semanticOutputDirectoryInfo.PSIsContainer -and
            ($semanticOutputDirectoryInfo.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -eq 0
        ) "Semantic bridge outer output directory is linked: $semanticOutputDirectory"
    }
    $null = Test-ExactPathHashInventory `
        -Records @($semanticResult.artifacts) `
        -ExpectedPaths $expectedSemanticArtifacts `
        -Root $semanticRunRoot `
        -Label 'Final semantic bridge artifact' `
        -Rehash
    $null = Test-ExactPathHashInventory `
        -Records @($semanticResult.logs) `
        -ExpectedPaths $expectedSemanticLogs `
        -Root $semanticRunRoot `
        -Label 'Final semantic bridge log' `
        -Rehash
    $SemanticBridgeRecordSha256 = $semantic.record_sha256
    $SemanticBridgeStdoutSha256 = Get-NormalizedTextSha256 -Text $semanticOutput
    Write-Host "CHECK SEMANTIC BRIDGE GATE OK result_sha256=$SemanticBridgeRunResultSha256"

    Invoke-Logged -Name 'terminal_plan' -Command $python `
        -Arguments @('-E', '-s', '-S', '-B', (Join-Path $fullSourcePlain 'verify_g001_terminal5_plan_v1.py'), '--plan-dir', $fullPlanPlain, '--workspace', $fullWorkspacePlain, '--source-dir', $fullSourcePlain) `
        -WorkingDirectory $fullSourcePlain `
        -ExpectedMarker 'G001_TERMINAL5_PLAN_V1_VERIFIED records=39030 search=39000 zero=30 bundles=192' `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.terminal_plan `
        -RequireEmptyStderr | Out-Null

    Invoke-Logged -Name 'prior_three_manifest' -Command $powershell `
        -Arguments @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', '.\verify_manifest.ps1') `
        -WorkingDirectory $priorThree -ExpectedMarker 'PRIOR_THREE_EVIDENCE_OK' `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.prior_three_manifest `
        -RequireEmptyStderr | Out-Null

    Invoke-Logged -Name 'configuration_3_strict_ledger_audit' -Command $python `
        -Arguments @(
            '-E', '-s', '-S', '-B',
            (Join-Path $ProofDir 'config3_repair\audit_config3_a2_archive.py'),
            '--workspace', $WorkspaceRoot,
            '--ledger-only'
        ) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedMarker 'CONFIG3_A2_LEDGER_ONLY_AUDIT_PASS' `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.configuration_3_strict_ledger_audit `
        -RequireEmptyStderr | Out-Null

    $oldAuditMode = $env:G001_AUDIT_MODE
    try {
        $env:G001_AUDIT_MODE = 'READ_ONLY_COVERAGE'
        Invoke-Logged -Name 'configuration_2' -Command $powershell `
            -Arguments @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', '.\work\a2_solver\verify_g001_row1_partition_coverage_portable.ps1') `
            -WorkingDirectory $priorThree -ExpectedMarker 'G001_ROW1_COVERAGE_OK' `
            -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.configuration_2 `
            -RequireEmptyStderr | Out-Null
        Invoke-Logged -Name 'configuration_8' -Command $powershell `
            -Arguments @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', '.\work\a2_solver\verify_g001_row7_partition_coverage.ps1') `
            -WorkingDirectory $priorThree -ExpectedMarker 'G001_ROW7_COVERAGE_OK' `
            -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.configuration_8 `
            -RequireEmptyStderr | Out-Null
    }
    finally {
        $env:G001_AUDIT_MODE = $oldAuditMode
    }
    Invoke-Logged -Name 'configuration_3' -Command $powershell `
        -Arguments @('-NoLogo', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', '.\work\a2_solver\verify_a2_partition_coverage.ps1') `
        -WorkingDirectory $priorThree `
        -ExpectedMarker 'STATUS=COVERAGE_OK ALL_EXPECTED_PARTITIONS_ZERO' `
        -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.configuration_3 `
        -RequireEmptyStderr | Out-Null

    $config3Fresh = $record.evidence.configuration3_fresh_result
    Require-Condition ($config3Fresh.status -eq 'PASS') `
        'Fresh Configuration 3 released evidence is not complete and pinned'
    foreach ($digestName in @(
        'release_record_sha256', 'release_sidecar_sha256', 'manifest_sha256',
        'run_result_sha256', 'run_result_sidecar_sha256', 'exporter_sha256',
        'verifier_sha256', 'split_harness_sha256', 'normalized_stdout_sha256'
    )) {
        Require-Condition ($config3Fresh.$digestName -match '^[0-9a-f]{64}$') `
            "Fresh Configuration 3 digest is malformed: $digestName"
    }
    $config3FreshRelease = Join-Path $WorkspaceRoot `
        ($config3Fresh.release_directory -replace '/', '\')
    $fixedConfig3FreshRelease = Join-Path $ProofDir `
        'config3_repair\evidence\full_preserved_v1'
    Require-Condition (Test-Path -LiteralPath $config3FreshRelease -PathType Container) `
        'Fresh Configuration 3 released evidence directory is missing'
    Require-Condition (
        (Resolve-Path -LiteralPath $config3FreshRelease).Path -eq
        (Resolve-Path -LiteralPath $fixedConfig3FreshRelease).Path
    ) 'Fresh Configuration 3 evidence is not in the fixed released directory'
    $config3Verifier = Join-Path $WorkspaceRoot `
        ($config3Fresh.verifier_path -replace '/', '\')
    Invoke-Logged -Name 'config3_a2_frozen_split_strict' -Command $python `
        -Arguments @(
            '-E', '-s', '-S', '-B', $config3Verifier,
            '--release-root', $config3FreshRelease
        ) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedUniqueLastMarker $config3Fresh.expected_marker `
        -ExpectedNormalizedStdoutSha256 $config3Fresh.normalized_stdout_sha256 `
        -RequireEmptyStderr | Out-Null
    foreach ($binding in @(
        [pscustomobject]@{
            Relative = $config3Fresh.release_record_path
            Sha256 = $config3Fresh.release_record_sha256
        },
        [pscustomobject]@{
            Relative = $config3Fresh.run_result_path
            Sha256 = $config3Fresh.run_result_sha256
        },
        [pscustomobject]@{
            Relative = $config3Fresh.manifest_path
            Sha256 = $config3Fresh.manifest_sha256
        },
        [pscustomobject]@{
            Relative = $config3Fresh.verifier_path
            Sha256 = $config3Fresh.verifier_sha256
        }
    )) {
        $boundPath = Get-ContainedPlainSingleLinkFile `
            -Root $WorkspaceRoot -Relative $binding.Relative `
            -Label 'Post-verification Config3 binding'
        $boundDigest = (Get-FileHash -Algorithm SHA256 -LiteralPath $boundPath).Hash.ToLowerInvariant()
        Require-Condition ($boundDigest -eq $binding.Sha256) `
            "Config3 binding changed during strict verification: $($binding.Relative)"
    }
    $Config3RunResultSha256 = $config3Fresh.run_result_sha256
    $Config3ReleaseRecordSha256 = $config3Fresh.release_record_sha256
    $Config3ReleaseManifestSha256 = $config3Fresh.manifest_sha256

    $globalMarker = $record.evidence.global_relocation_adapter.expected_marker
    if ($UseRecordedGlobalReplay) {
        $replayPath = Join-Path $WorkspaceRoot $record.evidence.recorded_global_replay.path
        $actualReplayHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $replayPath).Hash.ToLowerInvariant()
        Require-Condition ($actualReplayHash -eq $record.evidence.recorded_global_replay.sha256) 'Recorded global replay hash mismatch'
        $replayText = Get-Content -Raw -LiteralPath $replayPath
        $replayLines = @((
            $replayText -replace "`r`n", "`n" -replace "`r", "`n"
        ).Split("`n"))
        Require-Condition (
            @($replayLines | Where-Object { $_ -ceq $globalMarker }).Count -eq 1
        ) 'Recorded global replay marker is not one unique exact line'
        Write-Host 'CHECK RECORDED GLOBAL REPLAY ACCEPTED (full collector not rerun in this invocation)'
        $mode = 'recorded-global-replay'
        $finalMarker = 'LEECH18_HYBRID_RECORDED_REPLAY_PASS configurations=8 reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE'
    }
    else {
        $adapter = Join-Path $WorkspaceRoot $record.evidence.global_relocation_adapter.path
        Invoke-Logged -Name 'global_relocated_collector' -Command $python `
            -Arguments @('-E', '-s', '-S', '-B', $adapter, '--workspace', $fullWorkspace, '--plan-dir', $fullPlan, '--source-dir', $fullSource, '--run-root', $fullRun, '--expected-global-json', $expectedGlobal) `
            -WorkingDirectory $WorkspaceRoot -ExpectedUniqueLastMarker $globalMarker `
            -ExpectedNormalizedStdoutSha256 $record.evidence.normalized_stdout_sha256.global_relocated_collector `
            -RequireEmptyStderr | Out-Null
        $mode = 'full-global-replay'
        $finalMarker = 'LEECH18_HYBRID_END_TO_END_PASS configurations=8 reported_node_visits=8565199014 global_status=GLOBAL_ZERO_COMPLETE'
    }

    Invoke-Logged -Name 'hybrid_record_final' -Command $python `
        -Arguments @('-E', '-s', '-S', '-B', (Join-Path $ProofDir 'verify_hybrid_record.py')) `
        -WorkingDirectory $WorkspaceRoot `
        -ExpectedUniqueLastMarker 'LEECH18_HYBRID_RECORD_OK configurations=8 reported_node_visits=8565199014' `
        -RequireEmptyStderr | Out-Null
    Test-PackageManifest
    $finalPackageManifestSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath (Join-Path $ProofDir 'MANIFEST.sha256')).Hash.ToLowerInvariant()
    Require-Condition ($finalPackageManifestSha256 -eq $InitialPackageManifestSha256) `
        'Proof package manifest changed during the replay'
    Write-Host "CHECK PROOF PACKAGE STABLE sha256=$finalPackageManifestSha256"

    $requiredStageNames = if ($mode -eq 'full-global-replay') {
        $RequiredFullStageNames
    } else {
        @($RequiredFullStageNames | Where-Object {
            $_ -ne 'global_relocated_collector'
        })
    }
    $StageLogManifestSha256 = Write-StageLogManifest `
        -ExpectedStages $requiredStageNames
    Write-Host "CHECK STAGE LOG MANIFEST OK sha256=$StageLogManifestSha256"
    Write-Host $finalMarker
    Stop-Transcript | Out-Null
    $TranscriptStarted = $false
    Require-PlainSingleLinkFile -Path $TranscriptPath `
        -Label 'Outer transcript'
    $TranscriptSha256 = (Get-FileHash -Algorithm SHA256 `
        -LiteralPath $TranscriptPath).Hash.ToLowerInvariant()
    Write-RunResult -Mode $mode -ExitCode 0 -FinalMarker $finalMarker
    exit 0
}
catch {
    $failureMessage = $_.Exception.Message
    Write-Error "LEECH18_HYBRID_END_TO_END_FAIL $failureMessage" -ErrorAction Continue
    if ($TranscriptStarted) {
        try {
            Stop-Transcript | Out-Null
            $TranscriptStarted = $false
        }
        catch {
            Write-Warning "Could not stop transcript: $($_.Exception.Message)"
        }
    }
    if (Test-Path -LiteralPath $TranscriptPath -PathType Leaf) {
        $TranscriptSha256 = (Get-FileHash -Algorithm SHA256 `
            -LiteralPath $TranscriptPath).Hash.ToLowerInvariant()
    }
    try {
        Write-RunResult -Mode 'incomplete' -ExitCode 1 `
            -FinalMarker 'LEECH18_HYBRID_END_TO_END_FAIL' -Failure $failureMessage
    }
    catch {
        Write-Warning "Could not persist RUN_RESULT.txt: $($_.Exception.Message)"
    }
    exit 1
}
