param(
    [string] $Ledger = ''
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
if (-not $Ledger) {
    $Ledger = Join-Path $rootDir 'outputs\G001_ROW7_PARTITION_RESULTS.csv'
}
$fanout = Join-Path $rootDir 'outputs\G001_ROW7_PARTITION_FANOUT.csv'
$solver = Join-Path $solverDir 'order18_topology_free_search.exe'
$expectedSolverSha256 = `
    '9F894F39EFB71E9C8506E5C5B312289B1D3BEFE95C95B911DF8613F2E24BAFFB'

if (-not (Test-Path -LiteralPath $Ledger -PathType Leaf)) {
    throw "Missing ledger: $Ledger"
}
if (-not (Test-Path -LiteralPath $fanout -PathType Leaf)) {
    throw "Missing fan-out certificate: $fanout"
}
if (-not (Test-Path -LiteralPath $solver -PathType Leaf)) {
    throw "Missing production solver: $solver"
}
$solverSha256 = (Get-FileHash -LiteralPath $solver -Algorithm SHA256).Hash
if ($solverSha256 -ne $expectedSolverSha256) {
    throw "Production solver hash is $solverSha256, expected $expectedSolverSha256."
}

function Resolve-WorkspaceArtifact {
    param([string] $Path)
    if ([IO.Path]::IsPathRooted($Path)) { return $Path }
    return Join-Path $rootDir ($Path -replace '/', '\')
}

$expected = @(
    'root_0', 'root_1', 'root_2', 'path_3_0', 'path_3_1',
    'path_4_0', 'path_4_1', 'path_4_2', 'path_4_3', 'path_4_4',
    'path_4_5', 'path_4_6', 'path_4_7', 'path_4_8',
    'path_4_9_0', 'path_4_9_1', 'path_4_9_2', 'path_4_9_3',
    'path_4_9_4', 'path_4_9_5', 'path_4_9_6', 'path_4_9_7',
    'path_4_9_8', 'path_4_9_9', 'path_4_9_10', 'path_4_9_11',
    'path_4_9_12', 'path_4_9_13', 'path_4_9_14'
)
$expected += @(0..22 | ForEach-Object { "path_4_9_15_$_" })

$fanoutRows = @(Import-Csv -LiteralPath $fanout)
$rootFanout = $fanoutRows | Where-Object {
    $_.parent_depth -eq '3' -and $_.parent_key -eq 'root'
}
if (@($rootFanout).Count -ne 1 -or
    [int]$rootFanout.expected_valid_children -ne 5 -or
    $rootFanout.verification_status -ne 'VERIFIED') {
    throw 'Root fan-out certificate is not exactly VERIFIED=5.'
}
for ($root = 0; $root -le 4; ++$root) {
    $row = @($fanoutRows | Where-Object {
        $_.parent_depth -eq '4' -and $_.parent_key -eq [string]$root
    })
    $want = @(3,3,2,2,10)[$root]
    if ($row.Count -ne 1 -or
        [int]$row[0].expected_valid_children -ne $want -or
        $row[0].verification_status -ne 'VERIFIED') {
        throw "Bad depth-4 fan-out certificate for root $root."
    }
}
$row49 = @($fanoutRows | Where-Object {
    $_.parent_depth -eq '5' -and $_.parent_key -eq '4_9'
})
if ($row49.Count -ne 1 -or
    [int]$row49[0].expected_valid_children -ne 16 -or
    $row49[0].verification_status -ne 'VERIFIED') {
    throw 'Bad depth-5 fan-out certificate for path 4,9.'
}
$row4915 = @($fanoutRows | Where-Object {
    $_.parent_depth -eq '6' -and $_.parent_key -eq '4_9_15'
})
if ($row4915.Count -ne 1 -or
    [int]$row4915[0].expected_valid_children -ne 23 -or
    $row4915[0].verification_status -ne 'VERIFIED') {
    throw 'Bad depth-6 fan-out certificate for path 4,9,15.'
}

# Recompute the small fan-outs with the exact frozen production executable.
# The CSV is a human-readable certificate; these calls ensure it still agrees
# with the binary whose hash is required below.
if (Test-Path -LiteralPath 'C:\Ruby33-x64\msys64\ucrt64\bin') {
    $env:Path = 'C:\Ruby33-x64\msys64\ucrt64\bin;' +
        'C:\Ruby33-x64\msys64\usr\bin;' + $env:Path
}
$productionFlags = @(
    '--multi-edge-cover',
    '--multi-edge-cover-no-hall',
    '--multi-edge-cover-max-components', '6',
    '--multi-edge-cover-budget', '100',
    '--multi-edge-cover-no-exact-hall'
)
function Assert-ShallowFanout {
    param(
        [string] $SelectorKind,
        [string] $SelectorValue,
        [int] $StopEdges,
        [int] $ExpectedFrontier,
        [string] $ExpectedChildMax
    )
    $arguments = @('--mode','g001_row7')
    if ($SelectorKind) {
        $arguments += @($SelectorKind,$SelectorValue)
    }
    $arguments += @('--stop-edges',[string]$StopEdges)
    $arguments += $productionFlags
    $output = @(& $solver @arguments 2>&1)
    $solverExit = $LASTEXITCODE
    if ($solverExit -ne 0) {
        throw "Shallow fan-out command exited ${solverExit}: $($arguments -join ' ')"
    }
    $result = @($output | Where-Object {
        $_ -match '^RESULT mode=g001_row7 status=FRONTIER '
    })
    if ($result.Count -ne 1 -or
        $result[0] -notmatch "(?:^|\s)root_valid=5(?:\s|$)" -or
        $result[0] -notmatch "(?:^|\s)frontier=$ExpectedFrontier(?:\s|$)" -or
        $result[0] -notmatch "(?:^|\s)child_max=.*$([regex]::Escape($ExpectedChildMax))") {
        throw "Shallow fan-out mismatch: $($arguments -join ' ')"
    }
}

Assert-ShallowFanout '' '' 4 5 '3:5,'
$expectedRootChildren = @(3,3,2,2,10)
for ($root = 0; $root -le 4; ++$root) {
    Assert-ShallowFanout '--root-branch' ([string]$root) 5 `
        $expectedRootChildren[$root] "4:$($expectedRootChildren[$root]),"
}
Assert-ShallowFanout '--branch-path' '4,9' 6 16 '5:16,'
Assert-ShallowFanout '--branch-path' '4,9,15' 7 23 '6:23,'

$rows = @(Import-Csv -LiteralPath $Ledger)
$keys = @($rows | ForEach-Object { $_.key })
$duplicate = @($keys | Group-Object | Where-Object Count -ne 1)
if ($duplicate.Count) {
    throw "Duplicate ledger keys: $($duplicate.Name -join ', ')"
}

$missing = @($expected | Where-Object { $_ -notin $keys })
$unexpected = @($keys | Where-Object { $_ -notin $expected })

foreach ($row in $rows) {
    $expectedSelector = if ($row.key -match '^root_(\d+)$') {
        "--root-branch $($matches[1])"
    } elseif ($row.key -match '^path_(\d+(?:_\d+)+)$') {
        "--branch-path $($matches[1] -replace '_', ',')"
    } else {
        throw "Unrecognized partition key syntax: $($row.key)"
    }
    if ($row.selector -ne $expectedSelector) {
        throw "Partition $($row.key) has selector '$($row.selector)', expected '$expectedSelector'."
    }
    if ($row.status -ne 'ZERO') {
        throw "Partition $($row.key) is not ZERO: $($row.status)"
    }
    if ([int]$row.exit_code -ne 0) {
        throw "Partition $($row.key) has exit code $($row.exit_code)."
    }
    if ([int64]$row.nodes -le 0) {
        throw "Partition $($row.key) has no positive node count."
    }
    if ($row.solver_sha256 -ne $solverSha256) {
        throw "Partition $($row.key) used solver $($row.solver_sha256), expected $solverSha256."
    }
    $stdoutPath = Resolve-WorkspaceArtifact $row.stdout_path
    $stderrPath = Resolve-WorkspaceArtifact $row.stderr_path
    if (-not $row.stdout_path -or
        -not (Test-Path -LiteralPath $stdoutPath -PathType Leaf)) {
        throw "Partition $($row.key) has no readable stdout artifact."
    }
    if (-not $row.stderr_path -or
        -not (Test-Path -LiteralPath $stderrPath -PathType Leaf)) {
        throw "Partition $($row.key) has no readable stderr artifact."
    }
    if ((Get-Item -LiteralPath $stderrPath).Length -ne 0) {
        throw "Partition $($row.key) has nonempty stderr."
    }
    $pidPath = $stdoutPath -replace '\.stdout\.txt$', '.pid.txt'
    if ($pidPath -eq $stdoutPath -or
        -not (Test-Path -LiteralPath $pidPath -PathType Leaf)) {
        throw "Partition $($row.key) has no readable PID/argument artifact."
    }
    $expectedArguments = "arguments=--mode g001_row7 $expectedSelector " +
        '--multi-edge-cover --multi-edge-cover-no-hall ' +
        '--multi-edge-cover-max-components 6 ' +
        '--multi-edge-cover-budget 100 --multi-edge-cover-no-exact-hall'
    $argumentLines = @(Get-Content -LiteralPath $pidPath |
        Where-Object { $_ -like 'arguments=*' })
    if ($argumentLines.Count -ne 1 -or
        $argumentLines[0] -ne $expectedArguments) {
        throw "Partition $($row.key) does not record the exact production arguments."
    }
    $pidHashLines = @(Get-Content -LiteralPath $pidPath |
        Where-Object { $_ -like 'solver_sha256=*' })
    if ($pidHashLines.Count -ne 1 -or
        $pidHashLines[0] -ne "solver_sha256=$solverSha256") {
        throw "Partition $($row.key) PID metadata has the wrong solver hash."
    }
    $donePath = $stdoutPath -replace '\.stdout\.txt$', '.done.txt'
    if ($donePath -eq $stdoutPath -or
        -not (Test-Path -LiteralPath $donePath -PathType Leaf)) {
        throw "Partition $($row.key) has no readable done artifact."
    }
    $doneValues = @{}
    foreach ($line in Get-Content -LiteralPath $donePath) {
        if ($line -match '^([^=]+)=(.*)$') {
            $doneValues[$matches[1]] = $matches[2]
        }
    }
    if (-not $doneValues.ContainsKey('exit_code') -or
        -not $doneValues.ContainsKey('wall_seconds') -or
        [int]$doneValues.exit_code -ne [int]$row.exit_code -or
        [math]::Abs([double]$doneValues.wall_seconds -
            [double]$row.wall_seconds) -gt 1e-9) {
        throw "Partition $($row.key) ledger does not match its done artifact."
    }
    $result = @(Select-String -LiteralPath $stdoutPath `
        -Pattern '^RESULT mode=g001_row7 status=ZERO ')
    if ($result.Count -ne 1) {
        throw "Partition $($row.key) does not have exactly one ZERO RESULT."
    }
    if ($result[0].Line -notmatch '(?:^|\s)solution_topologies=0(?:\s|$)') {
        throw "Partition $($row.key) does not report solution_topologies=0."
    }
    $resultValues = @{}
    foreach ($match in [regex]::Matches(
        $result[0].Line, '(?:^|\s)([A-Za-z0-9_]+)=([^\s]+)')) {
        $resultValues[$match.Groups[1].Value] = $match.Groups[2].Value
    }
    foreach ($counter in @('nodes','states','generated')) {
        if (-not $resultValues.ContainsKey($counter) -or
            [int64]$resultValues[$counter] -ne [int64]$row.$counter) {
            throw "Partition $($row.key) ledger $counter does not match stdout."
        }
    }
}

if ($missing.Count -or $unexpected.Count) {
    Write-Output "EXPECTED=$($expected.Count) RECORDED=$($rows.Count)"
    if ($missing.Count) { Write-Output "MISSING=$($missing -join ',')" }
    if ($unexpected.Count) {
        Write-Output "UNEXPECTED=$($unexpected -join ',')"
    }
    exit 1
}

$nodeSum = ($rows | Measure-Object -Property nodes -Sum).Sum
$stateSum = ($rows | Measure-Object -Property states -Sum).Sum
$generatedSum = ($rows | Measure-Object -Property generated -Sum).Sum
$wallSum = ($rows | Measure-Object -Property wall_seconds -Sum).Sum
Write-Output "EXPECTED=$($expected.Count) RECORDED=$($rows.Count)"
Write-Output "NODE_SUM=$nodeSum STATE_SUM=$stateSum GENERATED_SUM=$generatedSum"
Write-Output "WALL_SUM_SECONDS=$wallSum"
Write-Output 'G001_ROW7_COVERAGE_OK'
