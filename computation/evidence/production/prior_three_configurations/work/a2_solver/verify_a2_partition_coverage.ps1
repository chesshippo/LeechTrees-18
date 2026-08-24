param(
    [string] $ResultsPath = (Join-Path $PSScriptRoot '..\..\outputs\A2_MULTI_EDGE_PARTITION_RESULTS.csv')
)

$ErrorActionPreference = 'Stop'
$expected = [System.Collections.Generic.List[string]]::new()

$expected.Add('a2_attached|root_0')
0..5 | ForEach-Object { $expected.Add("a2_attached|path_1_$_") }

0..3 | ForEach-Object { $expected.Add("a2_separate|root_$_") }
0..5 | ForEach-Object { $expected.Add("a2_separate|path_4_$_") }
0..4 | ForEach-Object { $expected.Add("a2_separate|path_5_$_") }
0..1 | ForEach-Object { $expected.Add("a2_separate|path_6_$_") }
0..7 | ForEach-Object { $expected.Add("a2_separate|path_7_$_") }
0..14 | ForEach-Object { $expected.Add("a2_separate|path_8_$_") }

$rows = @(Import-Csv -LiteralPath $ResultsPath)
$byKey = @{}
foreach ($row in $rows) {
    $key = "$($row.mode)|$($row.partition)"
    if ($byKey.ContainsKey($key)) {
        throw "Duplicate partition row: $key"
    }
    $byKey[$key] = $row
}

$missing = [System.Collections.Generic.List[string]]::new()
$invalid = [System.Collections.Generic.List[string]]::new()
foreach ($key in $expected) {
    if (-not $byKey.ContainsKey($key)) {
        $missing.Add($key)
        continue
    }
    $row = $byKey[$key]
    if ($row.status -ne 'ZERO' -or $row.exit_code -ne '0' -or [long]$row.nodes -le 0) {
        $invalid.Add("$key status=$($row.status) exit=$($row.exit_code) nodes=$($row.nodes)")
    }
}

if ($invalid.Count -gt 0) {
    $invalid | ForEach-Object { Write-Output "INVALID $_" }
    throw 'At least one covered partition lacks a valid ZERO certificate.'
}

$attached = @($rows | Where-Object mode -eq 'a2_attached')
$separate = @($rows | Where-Object mode -eq 'a2_separate')
$attachedNodes = ($attached | Measure-Object -Property nodes -Sum).Sum
$separateNodes = ($separate | Measure-Object -Property nodes -Sum).Sum

Write-Output "EXPECTED_PARTITIONS=$($expected.Count)"
Write-Output "RECORDED_PARTITIONS=$($rows.Count)"
Write-Output "ATTACHED_NODES=$attachedNodes"
Write-Output "SEPARATE_NODES=$separateNodes"
if ($missing.Count -gt 0) {
    Write-Output "STATUS=PARTIAL MISSING=$($missing.Count)"
    $missing | ForEach-Object { Write-Output "MISSING $_" }
    exit 1
}

Write-Output 'STATUS=COVERAGE_OK ALL_EXPECTED_PARTITIONS_ZERO'
