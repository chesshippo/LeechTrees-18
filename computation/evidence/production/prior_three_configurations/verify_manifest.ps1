$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$root = [IO.Path]::GetFullPath($PSScriptRoot)
$manifestPath = Join-Path $root 'MANIFEST.sha256'

function Require-Condition {
    param([bool]$Condition, [string]$Message)
    if (-not $Condition) { throw $Message }
}

function Get-RelativeUnixPath {
    param([string]$Base, [string]$Path)
    $baseUri = [Uri]($Base.TrimEnd('\') + '\')
    $pathUri = [Uri]$Path
    return [Uri]::UnescapeDataString($baseUri.MakeRelativeUri($pathUri).ToString())
}

Require-Condition (Test-Path -LiteralPath $manifestPath -PathType Leaf) `
    'Missing MANIFEST.sha256'
$manifestInfo = Get-Item -Force -LiteralPath $manifestPath
Require-Condition (
    ($manifestInfo.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0 -and
    [string]::IsNullOrEmpty([string]$manifestInfo.LinkType)
) 'MANIFEST.sha256 must be a plain file'

$raw = Get-Content -Raw -LiteralPath $manifestPath
Require-Condition (
    $raw.Length -gt 0 -and $raw.EndsWith("`n") -and -not $raw.Contains("`r")
) 'MANIFEST.sha256 must use canonical LF text'
$lines = @($raw.TrimEnd([char]10).Split("`n"))
$expected = [Collections.Generic.Dictionary[string,string]]::new(
    [StringComparer]::OrdinalIgnoreCase
)
$ordered = [Collections.Generic.List[string]]::new()
foreach ($line in $lines) {
    Require-Condition ($line -cmatch '^([0-9a-f]{64})  ([!-~]+)$') `
        "Malformed manifest line: $line"
    $digest = $Matches[1]
    $relative = $Matches[2]
    $parts = @($relative.Split('/'))
    Require-Condition (
        $relative -cne 'MANIFEST.sha256' -and
        $relative -notmatch '\\' -and
        -not [IO.Path]::IsPathRooted(($relative -replace '/', '\')) -and
        @($parts | Where-Object { $_ -eq '' -or $_ -eq '.' -or $_ -eq '..' }).Count -eq 0 -and
        -not $expected.ContainsKey($relative)
    ) "Unsafe or duplicate manifest path: $relative"
    $expected.Add($relative, $digest)
    $ordered.Add($relative)
}
$sorted = [string[]]$ordered.ToArray()
[Array]::Sort($sorted, [StringComparer]::Ordinal)
Require-Condition (($ordered -join "`n") -ceq ($sorted -join "`n")) `
    'MANIFEST.sha256 is not sorted by path'

$actual = [Collections.Generic.Dictionary[string,IO.FileInfo]]::new(
    [StringComparer]::OrdinalIgnoreCase
)
$totalBytes = [int64]0
foreach ($file in Get-ChildItem -LiteralPath $root -Recurse -Force -File) {
    Require-Condition (
        ($file.Attributes -band [IO.FileAttributes]::ReparsePoint) -eq 0 -and
        [string]::IsNullOrEmpty([string]$file.LinkType)
    ) "Evidence contains a linked file: $($file.FullName)"
    $relative = Get-RelativeUnixPath -Base $root -Path $file.FullName
    if ($relative -ceq 'MANIFEST.sha256') { continue }
    Require-Condition (-not $actual.ContainsKey($relative)) `
        "Evidence contains an aliased path: $relative"
    $actual.Add($relative, $file)
    $totalBytes += $file.Length
}

$missing = @($expected.Keys | Where-Object { -not $actual.ContainsKey($_) } | Sort-Object)
$extra = @($actual.Keys | Where-Object { -not $expected.ContainsKey($_) } | Sort-Object)
Require-Condition ($missing.Count -eq 0 -and $extra.Count -eq 0) `
    "Evidence file set mismatch: missing=$($missing -join ',') extra=$($extra -join ',')"
foreach ($relative in $ordered) {
    $digest = (Get-FileHash -Algorithm SHA256 -LiteralPath $actual[$relative].FullName).Hash.ToLowerInvariant()
    Require-Condition ($digest -ceq $expected[$relative]) `
        "SHA-256 mismatch: $relative"
}

$manifestHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $manifestPath).Hash.ToLowerInvariant()
Write-Output "FILES_VERIFIED=$($expected.Count)"
Write-Output "BYTES_VERIFIED=$totalBytes"
Write-Output "MANIFEST_SHA256=$manifestHash"
Write-Output 'PRIOR_THREE_EVIDENCE_OK'
