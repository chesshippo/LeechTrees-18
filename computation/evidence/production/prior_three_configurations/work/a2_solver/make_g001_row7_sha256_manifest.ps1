param(
    [string] $Output = ''
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
$ledgerPath = Join-Path $rootDir 'outputs\G001_ROW7_PARTITION_RESULTS.csv'
if (-not $Output) {
    $Output = Join-Path $rootDir `
        'outputs\G001_ROW7_EXHAUSTIVE_ZERO_SHA256SUMS.txt'
}

function Resolve-WorkspaceArtifact {
    param([string] $Path)
    if ([IO.Path]::IsPathRooted($Path)) { return $Path }
    return Join-Path $rootDir ($Path -replace '/', '\')
}

function Get-WorkspaceRelativePath {
    param([string] $Path)
    $absolute = (Resolve-Path -LiteralPath $Path).Path
    $prefix = $rootDir.TrimEnd('\') + '\'
    if (-not $absolute.StartsWith($prefix,
        [StringComparison]::OrdinalIgnoreCase)) {
        throw "Manifest input lies outside workspace: $absolute"
    }
    return $absolute.Substring($prefix.Length).Replace('\','/')
}

$verifier = Join-Path $solverDir 'verify_g001_row7_partition_coverage.ps1'
& powershell.exe -NoProfile -ExecutionPolicy Bypass -File $verifier
if ($LASTEXITCODE -ne 0) {
    throw 'Strict row-7 coverage verification failed; refusing to make manifest.'
}

$rows = @(Import-Csv -LiteralPath $ledgerPath)
if ($rows.Count -ne 52) {
    throw "Expected 52 ledger rows, found $($rows.Count)."
}

$relativeInputs = @(
    'work/a2_solver/order18_topology_free_search.exe',
    'work/a2_solver/order18_topology_free_search_production_snapshot.cpp',
    'work/a2_solver/a2_multi_edge_exact_cover.hpp',
    'work/a2_solver/a2_multi_edge_exact_cover_optimized.hpp',
    'work/a2_solver/a2_multi_edge_stronger_relaxation.hpp',
    'work/a2_solver/run_g001_row7_partition.ps1',
    'work/a2_solver/collect_g001_row7_result.ps1',
    'work/a2_solver/verify_g001_row7_partition_coverage.ps1',
    'work/a2_solver/make_g001_row7_sha256_manifest.ps1',
    'work/a2_solver/STRUCTURAL_RESTRICTIONS(1).md',
    'work/a2_solver/MULTI_EDGE_EXACT_COVER_DESIGN.md',
    'work/a2_solver/test_multi_edge_exact_cover.cpp',
    'work/a2_solver/test_multi_edge_exact_cover_small_orders.cpp',
    'outputs/G001_ROW7_PARTITION_RESULTS.csv',
    'outputs/G001_ROW7_PARTITION_FANOUT.csv',
    'outputs/G001_ROW7_FANOUT_VERIFICATION.txt',
    'outputs/G001_ROW7_BENCHMARK.csv',
    'outputs/G001_ROW7_ROOT4_CHILD_PROFILE.csv',
    'outputs/G001_ROW7_PRODUCTION_SOURCE_PROVENANCE.md',
    'outputs/G001_ROW7_COVERAGE_VERIFIER_TRANSCRIPT.txt',
    'outputs/G001_ROW7_FINAL_VALIDATION_TRANSCRIPT.txt'
)

foreach ($row in $rows) {
    $stdout = Resolve-WorkspaceArtifact $row.stdout_path
    foreach ($suffix in @('.stdout.txt','.stderr.txt','.pid.txt',
                           '.done.txt','.worker.ps1')) {
        $path = $stdout -replace '\.stdout\.txt$', $suffix
        if ($path -eq $stdout -and $suffix -ne '.stdout.txt') {
            throw "Cannot derive raw artifact from $stdout"
        }
        $relativeInputs += Get-WorkspaceRelativePath $path
    }
}

$relativeInputs = @($relativeInputs | Sort-Object -Unique)
$lines = foreach ($relative in $relativeInputs) {
    $absolute = Resolve-WorkspaceArtifact $relative
    if (-not (Test-Path -LiteralPath $absolute -PathType Leaf)) {
        throw "Missing manifest input: $relative"
    }
    $hash = (Get-FileHash -LiteralPath $absolute -Algorithm SHA256).Hash
    "$hash  $relative"
}

[IO.File]::WriteAllLines(
    $Output,
    [string[]]$lines,
    [Text.UTF8Encoding]::new($false)
)
$manifestHash = (Get-FileHash -LiteralPath $Output -Algorithm SHA256).Hash
Write-Output "MANIFEST_FILES=$($lines.Count)"
Write-Output "MANIFEST_SHA256=$manifestHash"
Write-Output "MANIFEST_PATH=$Output"
