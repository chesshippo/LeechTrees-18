param(
    [string] $Ledger = '',
    [string] $Plan = '',
    [string] $Fanout = '',
    [string] $Layer23Confirmation = '',
    [string] $Layer31Confirmation = '',
    [switch] $PlanOnly
)

$ErrorActionPreference = 'Stop'
$solverDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$rootDir = Split-Path -Parent (Split-Path -Parent $solverDir)
if (-not $Ledger) {
    $Ledger = Join-Path $rootDir 'outputs\G001_ROW1_PARTITION_RESULTS.csv'
}
if (-not $Plan) {
    $Plan = Join-Path $rootDir `
        'outputs\G001_ROW1_PARTITION_PLAN_PROVISIONAL.csv'
}
if (-not $Fanout) {
    $Fanout = Join-Path $rootDir `
        'outputs\G001_ROW1_PARTITION_FANOUT_PROVISIONAL.csv'
}
if (-not $Layer23Confirmation) {
    $Layer23Confirmation = Join-Path $rootDir `
        'outputs\G001_ROW1_PATH_2_9_15_PROFILE_CONFIRMATION.txt'
}
if (-not $Layer31Confirmation) {
    $Layer31Confirmation = Join-Path $rootDir `
        'outputs\G001_ROW1_PATH_2_9_15_22_PROFILE_CONFIRMATION.txt'
}

$solver = Join-Path $solverDir 'order18_topology_free_search_row1.exe'
$source = Join-Path $solverDir `
    'order18_topology_free_search_row1_snapshot.cpp'
$exactCoverHeader = Join-Path $solverDir 'a2_multi_edge_exact_cover.hpp'
$optimizedHeader = Join-Path $solverDir `
    'a2_multi_edge_exact_cover_optimized.hpp'
$strongerHeader = Join-Path $solverDir `
    'a2_multi_edge_stronger_relaxation.hpp'
$parityHeader = Join-Path $solverDir 'multi_edge_parity_coherence.hpp'

$expectedSolverSha256 = `
    '5F50BEC4D18947680EE170BF22AF747D1E74EA203E34E305EAE27768439B46AD'
$expectedSourceSha256 = `
    '134373D19AD4B1B1DFB30595F73BEABCEF30FA21C19B74A652669FB7705A72D9'
$expectedPlanSha256 = `
    '3CAC29583013A86A5951CB85B846F634EFA9E5791C55D4A3D59EF9E65A68C316'
$expectedFanoutSha256 = `
    'BCFA8A6AE25CEB7CCEC9597C7ABBEE9FF924060F8400DD09E47EAB2A33D4D58E'
$expectedPlanVersion = 'G001-ROW1-COVER-v3-PROVISIONAL-20260816'
$expectedPlanStatus = 'PROVISIONAL_DEEP_SPLIT_PROFILE_PENDING'

$expectedFileHashes = [ordered]@{
    $solver = $expectedSolverSha256
    $source = $expectedSourceSha256
    $exactCoverHeader = `
        'C156EAE52BCEEF28DB0DF1A38D10DEA253DE09E5F627D0952A6BB1B9356CD813'
    $optimizedHeader = `
        '5320C920E800CE2F9E2348B90D672E26CDDD748B43BC02BC24B9146DEDB5E48B'
    $strongerHeader = `
        'E58F917A631C48F2419835D41C2B0EE164F0D24F44BA489C152B9C00CDDBBD5C'
    $parityHeader = `
        'AF09E37C9E50FB3891BB11BBFEAD6D5F8299200C7ABF81BC8049FB20A07D30C7'
}

$productionFlags = @(
    '--multi-edge-cover',
    '--multi-edge-cover-no-hall',
    '--multi-edge-cover-max-components', '6',
    '--multi-edge-cover-budget', '100',
    '--multi-edge-cover-no-exact-hall'
)

function Assert-ExactOrderedStrings {
    param(
        [object[]] $Actual,
        [object[]] $Expected,
        [string] $Label
    )
    if ($Actual.Count -ne $Expected.Count) {
        throw "$Label count is $($Actual.Count), expected $($Expected.Count)."
    }
    for ($i = 0; $i -lt $Expected.Count; ++$i) {
        if ([string]$Actual[$i] -cne [string]$Expected[$i]) {
            throw "$Label item $i is '$($Actual[$i])', expected '$($Expected[$i])'."
        }
    }
}

function Assert-ExactSet {
    param(
        [object[]] $Actual,
        [object[]] $Expected,
        [string] $Label
    )
    $duplicate = @($Actual | Group-Object | Where-Object Count -ne 1)
    if ($duplicate.Count) {
        throw "$Label has duplicates: $($duplicate.Name -join ', ')."
    }
    $missing = @($Expected | Where-Object { $_ -notin $Actual })
    $unexpected = @($Actual | Where-Object { $_ -notin $Expected })
    if ($missing.Count -or $unexpected.Count -or
        $Actual.Count -ne $Expected.Count) {
        throw "$Label mismatch; missing=[$($missing -join ',')] unexpected=[$($unexpected -join ',')]."
    }
}

function Read-StrictKeyValueFile {
    param(
        [string] $Path,
        [string[]] $ExpectedKeys,
        [string] $Label
    )
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing $Label artifact: $Path"
    }
    $lines = @(Get-Content -LiteralPath $Path)
    if ($lines.Count -ne $ExpectedKeys.Count) {
        throw "$Label has $($lines.Count) lines, expected $($ExpectedKeys.Count)."
    }
    $values = [ordered]@{}
    for ($i = 0; $i -lt $lines.Count; ++$i) {
        if ($lines[$i] -notmatch '^([A-Za-z0-9_]+)=(.*)$') {
            throw "Malformed $Label line $($i + 1): $($lines[$i])"
        }
        $key = $matches[1]
        $value = $matches[2]
        if ($key -cne $ExpectedKeys[$i]) {
            throw "$Label key $i is '$key', expected '$($ExpectedKeys[$i])'."
        }
        if ($values.Contains($key)) {
            throw "Duplicate $Label key: $key"
        }
        $values[$key] = $value
    }
    return $values
}

function Get-ResultValues {
    param([string] $Line)
    $tokens = @($Line.Split(
        @(' '), [StringSplitOptions]::RemoveEmptyEntries))
    if ($tokens.Count -lt 2 -or $tokens[0] -cne 'RESULT') {
        throw "Malformed RESULT line: $Line"
    }
    $values = [ordered]@{}
    for ($i = 1; $i -lt $tokens.Count; ++$i) {
        $separator = $tokens[$i].IndexOf('=')
        if ($separator -le 0) {
            throw "Malformed RESULT token: $($tokens[$i])"
        }
        $key = $tokens[$i].Substring(0, $separator)
        $value = $tokens[$i].Substring($separator + 1)
        if ($key -notmatch '^[A-Za-z0-9_]+$' -or
            $values.Contains($key)) {
            throw "Invalid or duplicate RESULT key: $key"
        }
        $values[$key] = $value
    }
    return $values
}

function ConvertTo-StrictNonnegativeInt64 {
    param(
        [string] $Text,
        [string] $Label,
        [switch] $Positive
    )
    if ($Text -notmatch '^(?:0|[1-9][0-9]*)$') {
        throw "$Label is not a canonical nonnegative integer: '$Text'."
    }
    try { $value = [int64]::Parse($Text) }
    catch { throw "$Label is outside Int64 range: '$Text'." }
    if ($Positive -and $value -le 0) {
        throw "$Label must be positive."
    }
    return $value
}

function ConvertTo-StrictPositiveDouble {
    param(
        [string] $Text,
        [string] $Label
    )
    if ($Text -notmatch `
        '^(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[Ee][+-]?[0-9]+)?$') {
        throw "$Label is not a canonical nonnegative real: '$Text'."
    }
    try {
        $value = [double]::Parse(
            $Text, [Globalization.CultureInfo]::InvariantCulture)
    } catch { throw "$Label is not a finite floating-point number: '$Text'." }
    if ([double]::IsNaN($value) -or [double]::IsInfinity($value) -or
        $value -le 0) {
        throw "$Label must be positive and finite."
    }
    return $value
}

function ConvertTo-RoundTripTimestamp {
    param(
        [string] $Text,
        [string] $Label
    )
    try {
        return [DateTimeOffset]::Parse(
            $Text,
            [Globalization.CultureInfo]::InvariantCulture,
            [Globalization.DateTimeStyles]::RoundtripKind)
    } catch { throw "$Label is not a round-trip timestamp: '$Text'." }
}

function Get-SelectorArguments {
    param([string] $Selector)
    if ($Selector -match '^root:([0-2])$') {
        return @('--root-branch', $matches[1])
    }
    if ($Selector -match `
        '^path:((?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*))*)$') {
        $path = $matches[1]
        if ([int]($path.Split(',')[0]) -gt 2) {
            throw "Selector starts outside the three root children: $Selector"
        }
        return @('--branch-path', $path)
    }
    throw "Invalid canonical selector: $Selector"
}

function Convert-SelectorToPath {
    param([string] $Selector)
    $arguments = @(Get-SelectorArguments $Selector)
    if ($arguments[0] -eq '--root-branch') {
        return ,@([int]$arguments[1])
    }
    return ,@($arguments[1].Split(',') | ForEach-Object { [int]$_ })
}

function Test-StrictPrefix {
    param(
        [object[]] $Left,
        [object[]] $Right
    )
    if ($Left.Count -ge $Right.Count) { return $false }
    for ($i = 0; $i -lt $Left.Count; ++$i) {
        if ([int]$Left[$i] -ne [int]$Right[$i]) { return $false }
    }
    return $true
}

foreach ($entry in $expectedFileHashes.GetEnumerator()) {
    if (-not (Test-Path -LiteralPath $entry.Key -PathType Leaf)) {
        throw "Missing frozen implementation artifact: $($entry.Key)"
    }
    $actualHash = (Get-FileHash -LiteralPath $entry.Key `
        -Algorithm SHA256).Hash
    if ($actualHash -cne $entry.Value) {
        throw "Hash mismatch for $($entry.Key): $actualHash"
    }
}

# These two branches are the fail-open exits for candidate-cap and DP-budget
# exhaustion.  Their frozen hash is checked above; this textual guard makes
# the intended UNKNOWN/PASS semantics explicit in the certificate verifier.
$exactCoverText = Get-Content -Raw -LiteralPath $exactCoverHeader
$unknownPassCount = [regex]::Matches(
    $exactCoverText, 'return \{true, Reason::exact_unknown\};').Count
if ($unknownPassCount -ne 2) {
    throw 'Frozen exact-cover header no longer has both fail-open UNKNOWN exits.'
}

if (-not (Test-Path -LiteralPath $Plan -PathType Leaf)) {
    throw "Missing frozen provisional plan: $Plan"
}
$planSha256 = (Get-FileHash -LiteralPath $Plan -Algorithm SHA256).Hash
if ($planSha256 -cne $expectedPlanSha256) {
    throw "Plan hash is $planSha256, expected $expectedPlanSha256."
}

$expectedPlan = [ordered]@{}
$expectedPlan['root_0'] = 'root:0'
$expectedPlan['root_1'] = 'root:1'
foreach ($child in 0..8) {
    $expectedPlan["path_2_$child"] = "path:2,$child"
}
foreach ($child in 0..14) {
    $expectedPlan["path_2_9_$child"] = "path:2,9,$child"
}
foreach ($child in 0..21) {
    $expectedPlan["path_2_9_15_$child"] = "path:2,9,15,$child"
}
foreach ($child in 0..30) {
    $expectedPlan["path_2_9_15_22_$child"] = `
        "path:2,9,15,22,$child"
}
$expectedKeys = @($expectedPlan.Keys)
$expectedSelectors = @($expectedPlan.Values)

$planRows = @(Import-Csv -LiteralPath $Plan)
if ($planRows.Count -eq 0) { throw 'The partition plan is empty.' }
$expectedPlanColumns = @(
    'plan_version','plan_status','key','selector','coverage_parent',
    'child_index','notes'
)
Assert-ExactOrderedStrings `
    @($planRows[0].PSObject.Properties.Name) $expectedPlanColumns `
    'plan columns'
Assert-ExactSet @($planRows | ForEach-Object key) $expectedKeys 'plan keys'
Assert-ExactSet @($planRows | ForEach-Object selector) `
    $expectedSelectors 'plan selectors'

for ($i = 0; $i -lt $expectedKeys.Count; ++$i) {
    $row = $planRows[$i]
    $key = $expectedKeys[$i]
    $selector = $expectedPlan[$key]
    if ($row.key -cne $key -or $row.selector -cne $selector) {
        throw "Plan row $i is not the frozen ordered partition $key/$selector."
    }
    if ($row.plan_version -cne $expectedPlanVersion -or
        $row.plan_status -cne $expectedPlanStatus) {
        throw "Plan row $key has an unexpected version/status."
    }
    $expectedParent = if ($key -match '^root_') {
        'seed'
    } elseif ($key -match '^path_2_[0-8]$') {
        'root_2'
    } elseif ($key -match '^path_2_9_(?:[0-9]|1[0-4])$') {
        'path_2_9'
    } elseif ($key -match '^path_2_9_15_(?:[0-9]|1[0-9]|2[01])$') {
        'path_2_9_15'
    } else {
        'path_2_9_15_22'
    }
    $expectedChild = if ($key -match '_(\d+)$') { $matches[1] }
    else { throw "Cannot derive child index for $key." }
    if ($row.coverage_parent -cne $expectedParent -or
        $row.child_index -cne $expectedChild) {
        throw "Plan row $key has an incorrect coverage-parent binding."
    }
}

if (-not (Test-Path -LiteralPath $Fanout -PathType Leaf)) {
    throw "Missing frozen provisional fan-out certificate: $Fanout"
}
$fanoutSha256 = (Get-FileHash -LiteralPath $Fanout -Algorithm SHA256).Hash
if ($fanoutSha256 -cne $expectedFanoutSha256) {
    throw "Fan-out hash is $fanoutSha256, expected $expectedFanoutSha256."
}
$fanoutRows = @(Import-Csv -LiteralPath $Fanout)
if ($fanoutRows.Count -ne 5) {
    throw "Fan-out certificate has $($fanoutRows.Count) rows, expected 5."
}
$expectedFanoutColumns = @(
    'parent_depth','parent_key','selector','stop_edges',
    'expected_valid_children','verification_status','notes'
)
Assert-ExactOrderedStrings `
    @($fanoutRows[0].PSObject.Properties.Name) $expectedFanoutColumns `
    'fan-out columns'
$fanoutSpecs = @(
    @('3','seed','none','4','3'),
    @('4','root_2','root:2','5','10'),
    @('5','path_2_9','path:2,9','6','16'),
    @('6','path_2_9_15','path:2,9,15','7','23'),
    @('7','path_2_9_15_22','path:2,9,15,22','8','31')
)
for ($i = 0; $i -lt $fanoutSpecs.Count; ++$i) {
    $row = $fanoutRows[$i]
    $spec = $fanoutSpecs[$i]
    $actual = @(
        $row.parent_depth,$row.parent_key,$row.selector,$row.stop_edges,
        $row.expected_valid_children
    )
    Assert-ExactOrderedStrings $actual $spec "fan-out row $i"
    if ($row.verification_status -cne 'VERIFIED_FROZEN_EXECUTABLE') {
        throw "Fan-out row $i is not verified with the frozen executable."
    }
}

$selectorPaths = @{}
foreach ($key in $expectedKeys) {
    $selectorPaths[$key] = @(Convert-SelectorToPath $expectedPlan[$key])
}
for ($i = 0; $i -lt $expectedKeys.Count; ++$i) {
    for ($j = $i + 1; $j -lt $expectedKeys.Count; ++$j) {
        $left = $selectorPaths[$expectedKeys[$i]]
        $right = $selectorPaths[$expectedKeys[$j]]
        if ((Test-StrictPrefix $left $right) -or
            (Test-StrictPrefix $right $left)) {
            throw "Plan is not prefix-free: $($expectedKeys[$i]) / $($expectedKeys[$j])."
        }
    }
}

if (Test-Path -LiteralPath 'C:\Ruby33-x64\msys64\ucrt64\bin') {
    $env:Path = 'C:\Ruby33-x64\msys64\ucrt64\bin;' +
        'C:\Ruby33-x64\msys64\usr\bin;' + $env:Path
}

function Assert-ShallowFanout {
    param(
        [string[]] $SelectorArguments,
        [int] $StopEdges,
        [int] $ExpectedFrontier,
        [string] $ExpectedChildMax,
        [string] $Label,
        [string] $ExpectedFrontierMex = ''
    )
    $arguments = @('--mode','g001_row1')
    if ($SelectorArguments.Count) { $arguments += $SelectorArguments }
    $arguments += @('--stop-edges',[string]$StopEdges)
    $arguments += $productionFlags
    $output = @(& $solver @arguments 2>&1 | ForEach-Object { [string]$_ })
    $solverExit = $LASTEXITCODE
    if ($solverExit -ne 0 -or $output.Count -ne 1) {
        throw "$Label fan-out failed: exit=$solverExit lines=$($output.Count)."
    }
    $result = Get-ResultValues $output[0]
    foreach ($required in @(
        'mode','status','nodes','root_valid','frontier','multi_cover',
        'cover_validation_fail','cutlower','cutupper','late_t9a','child_max')) {
        if (-not $result.Contains($required)) {
            throw "$Label fan-out RESULT lacks $required."
        }
    }
    if ($result.mode -cne 'g001_row1' -or
        $result.status -cne 'FRONTIER' -or
        $result.multi_cover -cne 'on' -or
        $result.root_valid -cne '3' -or
        $result.frontier -cne [string]$ExpectedFrontier -or
        $result.cover_validation_fail -cne '0' -or
        $result.cutlower -cne '0' -or $result.cutupper -cne '0' -or
        $result.late_t9a -cne '0' -or
        $result.child_max -notmatch `
            "(?:^|,)$([regex]::Escape($ExpectedChildMax))(?:,|$)") {
        throw "$Label fan-out RESULT does not match the frozen expectation."
    }
    if ($ExpectedFrontierMex -and
        (-not $result.Contains('frontier_mex') -or
        $result.frontier_mex -cne $ExpectedFrontierMex)) {
        throw "$Label fan-out has an unexpected MEX distribution."
    }
    ConvertTo-StrictNonnegativeInt64 $result.nodes "$Label fan-out nodes" `
        -Positive | Out-Null
    Write-Output "FANOUT_OK label=$Label frontier=$ExpectedFrontier"
}

# Seed depth is three.  These five calls independently establish that the
# leaves in the provisional table are an exact disjoint cover: children 0
# and 1 are whole; child 2 has ten children; its child 9 has sixteen; and
# child 2,9,15 has twenty-three.  Its oversized child 22 is replaced by all
# thirty-one children.
Assert-ShallowFanout @() 4 3 '3:3' 'seed'
Assert-ShallowFanout @('--root-branch','2') 5 10 '4:10' 'root_2'
Assert-ShallowFanout @('--branch-path','2,9') 6 16 '5:16' 'path_2_9'
Assert-ShallowFanout @('--branch-path','2,9,15') 7 23 '6:23' `
    'path_2_9_15'
Assert-ShallowFanout @('--branch-path','2,9,15,22') 8 31 '7:31' `
    'path_2_9_15_22' '12:21,13:5,14:5,'

Write-Output "PLAN_SHA256=$planSha256"
Write-Output "FANOUT_SHA256=$fanoutSha256"
Write-Output "PLAN_ROWS=$($planRows.Count) PREFIX_FREE=YES"

if ($PlanOnly) {
    Write-Output 'PLAN_STATUS=PROVISIONAL_DEEP_SPLIT_PROFILE_PENDING'
    Write-Output 'NO_EXCLUSION_CLAIM=YES'
    Write-Output 'G001_ROW1_PROVISIONAL_PLAN_STRUCTURE_OK'
    return
}

# The confirmations are accepted only through an independently hash-pinned
# verifier that recomputes every CSV aggregate and binds every CSV, log, lock,
# stdout, stderr, and done artifact to a frozen SHA-256 manifest.  Node sums
# are never compared because selected-child jobs repeat their prefixes.
$profileEvidenceVerifier = Join-Path $solverDir `
    'verify_g001_row1_profile_evidence.ps1'
$expectedProfileEvidenceVerifierSha256 = `
    '91296DDB7635C8D1683BE4F48B7976638FDDCC0D3BBD1E580040F2EF3969963F'
if (-not (Test-Path -LiteralPath $profileEvidenceVerifier -PathType Leaf)) {
    throw "Missing profile-evidence verifier: $profileEvidenceVerifier"
}
$profileEvidenceVerifierSha256 = (Get-FileHash `
    -LiteralPath $profileEvidenceVerifier -Algorithm SHA256).Hash
if ($profileEvidenceVerifierSha256 -cne
    $expectedProfileEvidenceVerifierSha256) {
    throw "Profile-evidence verifier hash mismatch: $profileEvidenceVerifierSha256"
}
$evidenceOutput = @(& powershell.exe -NoLogo -NoProfile -NonInteractive `
    -ExecutionPolicy Bypass -File $profileEvidenceVerifier `
    -Layer23Confirmation $Layer23Confirmation `
    -Layer31Confirmation $Layer31Confirmation 2>&1 |
    ForEach-Object { [string]$_ })
$evidenceExit = $LASTEXITCODE
if ($evidenceExit -ne 0 -or
    @($evidenceOutput | Where-Object {
        $_ -ceq 'G001_ROW1_PROFILE_EVIDENCE_OK'
    }).Count -ne 1) {
    throw "Profile evidence verification failed (exit $evidenceExit): $($evidenceOutput -join ' | ')"
}
$evidenceOutput | Write-Output

if (-not (Test-Path -LiteralPath $Ledger -PathType Leaf)) {
    throw "Missing row-1 production ledger: $Ledger"
}
$rows = @(Import-Csv -LiteralPath $Ledger)
if ($rows.Count -eq 0) { throw 'The row-1 production ledger is empty.' }
$ledgerColumns = @(
    'key','selector','status','exit_code','nodes','states','generated',
    'wall_seconds','stdout_path','stderr_path','solver_sha256','arguments',
    'notes'
)
Assert-ExactOrderedStrings @($rows[0].PSObject.Properties.Name) `
    $ledgerColumns 'ledger columns'
Assert-ExactSet @($rows | ForEach-Object key) $expectedKeys 'ledger keys'
Assert-ExactSet @($rows | ForEach-Object selector) `
    $expectedSelectors 'ledger selectors'

$resultColumns = @(
    'mode','status','nodes','states','generated','duplicate','collision',
    'range','parity','diameter','g002','cutlower','cutupper','late_t9a',
    'solution_topologies','depth','root_valid','frontier','frontier_mex',
    'frontier_odd','frontier_q3','multi_cover','cover_checks',
    'cover_skipped','cover_skipped_full','cover_local_slots',
    'cover_local_patterns','cover_slots','cover_patterns',
    'cover_candidates','cover_no_candidate','cover_hall_fail',
    'cover_exact_calls','cover_exact_fail','cover_exact_pass',
    'cover_exact_budget','cover_exact_cap','cover_exact_states',
    'cover_exact_hall_fail','cover_validation_fail','cover_shadow_reject',
    'child_max'
)
$integerResultColumns = @(
    'nodes','states','generated','duplicate','collision','range','parity',
    'diameter','g002','cutlower','cutupper','late_t9a',
    'solution_topologies','root_valid','frontier','cover_checks',
    'cover_skipped','cover_skipped_full','cover_local_slots',
    'cover_local_patterns','cover_slots','cover_patterns',
    'cover_candidates','cover_no_candidate','cover_hall_fail',
    'cover_exact_calls','cover_exact_fail','cover_exact_pass',
    'cover_exact_budget','cover_exact_cap','cover_exact_states',
    'cover_exact_hall_fail','cover_validation_fail','cover_shadow_reject'
)
$aggregateColumns = @(
    'nodes','states','generated','cover_checks','cover_skipped',
    'cover_skipped_full','cover_local_slots','cover_local_patterns',
    'cover_slots','cover_patterns','cover_candidates','cover_no_candidate',
    'cover_hall_fail','cover_exact_calls','cover_exact_fail',
    'cover_exact_pass','cover_exact_budget','cover_exact_cap',
    'cover_exact_states','cover_exact_hall_fail'
)
$aggregate = [ordered]@{}
foreach ($counter in $aggregateColumns) { $aggregate[$counter] = [decimal]0 }
$wallSum = [decimal]0
$jobStems = @()
$stdoutArtifacts = @()
$stderrArtifacts = @()

foreach ($key in $expectedKeys) {
    $matching = @($rows | Where-Object key -CEQ $key)
    if ($matching.Count -ne 1) {
        throw "Expected exactly one ledger row for $key."
    }
    $row = $matching[0]
    $selector = $expectedPlan[$key]
    if ($row.selector -cne $selector -or $row.status -cne 'ZERO' -or
        $row.exit_code -cne '0') {
        throw "$key is not bound to an exit-0 ZERO result."
    }
    if ($row.solver_sha256 -cne $expectedSolverSha256) {
        throw "$key records the wrong solver hash."
    }
    $selectorArguments = @(Get-SelectorArguments $selector)
    $argumentTokens = @('--mode','g001_row1') + $selectorArguments +
        $productionFlags
    $expectedArguments = $argumentTokens -join ' '
    if ($row.arguments -cne $expectedArguments) {
        throw "$key ledger arguments do not equal the exact production argv."
    }
    if ($row.notes -cne `
        'uncapped; production exact-cover flags; stderr empty') {
        throw "$key has unexpected ledger notes."
    }
    if ($row.stdout_path -notmatch `
        '^work/a2_solver/row1_partition_runs/([A-Za-z0-9][A-Za-z0-9_.-]*)\.stdout\.txt$') {
        throw "$key has a noncanonical stdout path."
    }
    $jobStem = $matches[1]
    $expectedStderrRelative = `
        "work/a2_solver/row1_partition_runs/$jobStem.stderr.txt"
    if ($row.stderr_path -cne $expectedStderrRelative) {
        throw "$key stdout/stderr job stems differ."
    }
    $jobStems += $jobStem
    $stdoutArtifacts += $row.stdout_path
    $stderrArtifacts += $row.stderr_path

    $stdoutPath = Join-Path $rootDir ($row.stdout_path -replace '/', '\')
    $stderrPath = Join-Path $rootDir ($row.stderr_path -replace '/', '\')
    $pidPath = $stdoutPath -replace '\.stdout\.txt$', '.pid.txt'
    $donePath = $stdoutPath -replace '\.stdout\.txt$', '.done.txt'
    $doneTmpPath = $stdoutPath -replace '\.stdout\.txt$', '.done.tmp'
    foreach ($artifact in @(
        $stdoutPath,$stderrPath,$pidPath,$donePath)) {
        if (-not (Test-Path -LiteralPath $artifact -PathType Leaf)) {
            throw "$key is missing raw artifact: $artifact"
        }
        $resolved = (Resolve-Path -LiteralPath $artifact).Path
        $workspacePrefix = $rootDir.TrimEnd('\') + '\'
        if (-not $resolved.StartsWith(
            $workspacePrefix, [StringComparison]::OrdinalIgnoreCase)) {
            throw "$key artifact escapes the workspace: $resolved"
        }
    }
    if (Test-Path -LiteralPath $doneTmpPath) {
        throw "$key retains an incomplete .done.tmp artifact."
    }
    if ((Get-Item -LiteralPath $stderrPath).Length -ne 0) {
        throw "$key has nonempty solver stderr."
    }

    $pidKeys = @(
        'worker_pid','started_local','solver_sha256','source_sha256',
        'arguments'
    )
    $pidValues = Read-StrictKeyValueFile $pidPath $pidKeys "$key PID"
    ConvertTo-StrictNonnegativeInt64 $pidValues.worker_pid `
        "$key worker PID" -Positive | Out-Null
    $startedAt = ConvertTo-RoundTripTimestamp $pidValues.started_local `
        "$key start time"
    if ($pidValues.solver_sha256 -cne $expectedSolverSha256 -or
        $pidValues.source_sha256 -cne $expectedSourceSha256 -or
        $pidValues.arguments -cne $expectedArguments) {
        throw "$key PID metadata does not bind the frozen source/exe/argv."
    }

    $doneKeys = @('exit_code','wall_seconds','ended_local')
    $doneValues = Read-StrictKeyValueFile $donePath $doneKeys "$key done"
    if ($doneValues.exit_code -cne '0') {
        throw "$key done artifact has nonzero exit code."
    }
    $doneWall = ConvertTo-StrictPositiveDouble $doneValues.wall_seconds `
        "$key done wall time"
    $endedAt = ConvertTo-RoundTripTimestamp $doneValues.ended_local `
        "$key end time"
    if ($endedAt -lt $startedAt) {
        throw "$key ends before its recorded start time."
    }
    $ledgerWall = ConvertTo-StrictPositiveDouble $row.wall_seconds `
        "$key ledger wall time"
    $wallTolerance = 1e-9 * [math]::Max(1.0,
        [math]::Max([math]::Abs($doneWall), [math]::Abs($ledgerWall)))
    if ([math]::Abs($doneWall - $ledgerWall) -gt $wallTolerance) {
        throw "$key ledger wall time does not match its done artifact."
    }

    $stdoutLines = @(Get-Content -LiteralPath $stdoutPath)
    if ($stdoutLines.Count -ne 1) {
        throw "$key stdout has $($stdoutLines.Count) lines, expected one."
    }
    $result = Get-ResultValues $stdoutLines[0]
    Assert-ExactSet @($result.Keys) $resultColumns "$key RESULT fields"
    if ($result.mode -cne 'g001_row1' -or $result.status -cne 'ZERO' -or
        $result.multi_cover -cne 'on') {
        throw "$key raw RESULT is not active-cover row-1 ZERO."
    }
    foreach ($counter in $integerResultColumns) {
        ConvertTo-StrictNonnegativeInt64 $result[$counter] `
            "$key $counter" | Out-Null
    }
    foreach ($counter in @('nodes','states','generated','cover_checks')) {
        ConvertTo-StrictNonnegativeInt64 $result[$counter] `
            "$key $counter" -Positive | Out-Null
    }
    if ($result.solution_topologies -cne '0' -or
        $result.frontier -cne '0' -or
        $result.frontier_mex -cne '' -or
        $result.frontier_odd -cne '' -or
        $result.frontier_q3 -cne '' -or
        $result.root_valid -cne '3') {
        throw "$key does not have terminal ZERO/frontier/root invariants."
    }
    if ($result.cutlower -cne '0' -or $result.cutupper -cne '0' -or
        $result.late_t9a -cne '0' -or $result.cover_hall_fail -cne '0' -or
        $result.cover_exact_hall_fail -cne '0' -or
        $result.cover_validation_fail -cne '0' -or
        $result.cover_shadow_reject -cne '0') {
        throw "$key activated a forbidden layer or violated cover invariants."
    }
    if ($result.depth -notmatch '^(?:[0-9]+:[0-9]+,)+$' -or
        $result.child_max -notmatch '^(?:[0-9]+:[0-9]+,)+$' -or
        $result.depth -notmatch '(?:^|,)3:1,') {
        throw "$key has malformed search-depth diagnostics."
    }
    foreach ($counter in @('nodes','states','generated')) {
        if ([int64]$result[$counter] -ne [int64]$row.$counter) {
            throw "$key ledger $counter does not match raw stdout."
        }
    }
    foreach ($counter in $aggregateColumns) {
        $aggregate[$counter] += [decimal]([int64]$result[$counter])
    }
    $wallSum += [decimal]$ledgerWall
}

Assert-ExactSet $jobStems $jobStems 'job stems'
Assert-ExactSet $stdoutArtifacts $stdoutArtifacts 'stdout artifacts'
Assert-ExactSet $stderrArtifacts $stderrArtifacts 'stderr artifacts'

Write-Output "EXPECTED=$($expectedKeys.Count) RECORDED=$($rows.Count)"
Write-Output "NODE_SUM=$($aggregate.nodes) STATE_SUM=$($aggregate.states) GENERATED_SUM=$($aggregate.generated)"
Write-Output "WALL_SUM_SECONDS=$wallSum"
Write-Output "COVER_CHECKS_SUM=$($aggregate.cover_checks) COVER_CANDIDATES_SUM=$($aggregate.cover_candidates)"
Write-Output "COVER_REJECT_SUM=$($aggregate.cover_no_candidate + $aggregate.cover_exact_fail)"
Write-Output "FAIL_OPEN_UNKNOWN_SUM=$($aggregate.cover_exact_budget + $aggregate.cover_exact_cap)"
Write-Output 'FAIL_OPEN_POLICY=budget_or_candidate_cap_means_UNKNOWN_AND_PASS'
Write-Output 'G001_ROW1_COVERAGE_OK'
