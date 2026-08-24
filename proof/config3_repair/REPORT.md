# Configuration 3 / A2 certificate

## Result

Configuration 3 is excluded by a strict, relocatable certificate for the
exact 47-partition A2 roster. The release contains 46 direct `ZERO` receipts
and replaces the remaining memory-guarded parent partition,
`a2_separate/path_8_14`, with a complete census and 22 child `ZERO` receipts.

The release is:

```text
proof/config3_repair/evidence/full_preserved_v1/
```

It uses schema `config3-a2-frozen-split-release-v1` and contains 281 files in
73 directories including the root. Its 280-entry manifest covers every file
except the manifest itself.

| Object | SHA-256 |
|---|---|
| `MANIFEST.sha256` | `1603fe0bd5d6fee4e47d063a7077690ee76525631e31cc9d555aee71e59a53af` |
| `RELEASE.json` | `ef7addf3ba82b933ae780c57cc8fc633073b422075fbd98171ebabf78da57ae5` |
| `RUN_RESULT.json` | `c0b89376528fdc18881bc82ae9df6cf6632c913f8b1981de9014ef71cbb6f128` |
| `verify_config3_a2_frozen.py` | `2e739732b35ed7bb6e7dbeb174ee2e713eae4b691a518ee00c5f7644bfd0a38a` |

`RELEASE.json` binds the ordered logical roster, source and executable
identities, exact argument vectors, fan-out semantics, raw receipts, and node
identity. `RUN_RESULT.json` binds the 46 direct receipts, the census receipt,
and all 22 child receipts.

## Exact logical roster

- `a2_attached`: `root_0`, `path_1_0..5` (7 partitions).
- `a2_separate`: `root_0..3`, `path_4_0..5`, `path_5_0..4`,
  `path_6_0..1`, `path_7_0..7`, `path_8_0..14` (40 partitions).

The 46 direct receipts report 124,893,923 node calls. The child receipts for
`path_8_14` report 42,848,972 calls. The child prefixes duplicate three shared
calls at edge depths 4, 5, and 6, so the normalized parent count is

```text
42,848,972 - 3*(22-1) = 42,848,909.
```

Therefore the reconstructed logical total is

```text
124,893,923 + 42,848,909 = 167,742,832.
```

The census fixes the child roster `k = 0,...,21`; it is not itself a zero
certificate. Every child has a separate observed exit-0 receipt, empty stderr,
and exactly one `ZERO` result.

## Verification

From the repository root:

```powershell
python -E -s -S -B `
  .\proof\config3_repair\verify_config3_a2_frozen.py `
  --release-root `
  .\proof\config3_repair\evidence\full_preserved_v1
```

The verifier succeeds only with this sole output line:

```text
CONFIG3_A2_FROZEN_SPLIT_STRICT_OK schema=config3-a2-frozen-split-release-v1 logical_partitions=47 direct=46 children=22 logical_nodes=167742832 manifest_sha256=1603fe0bd5d6fee4e47d063a7077690ee76525631e31cc9d555aee71e59a53af release_sha256=ef7addf3ba82b933ae780c57cc8fc633073b422075fbd98171ebabf78da57ae5 run_result_sha256=c0b89376528fdc18881bc82ae9df6cf6632c913f8b1981de9014ef71cbb6f128
```

It rejects duplicate JSON keys, unsafe or aliased paths, links, junction
ancestors, hardlinks, extra or missing files, nonzero exits, non-`ZERO`
results, nonempty stderr, source or executable binding disagreement, roster
disagreement, node-accounting disagreement, and any final rehash change.

The legacy ledger can be audited independently:

```powershell
python -E -s -S -B `
  .\proof\config3_repair\audit_config3_a2_archive.py --ledger-only
```

That audit requires 47 exact ordered keys, no duplicates or extras, recorded
status `ZERO`, recorded exit 0, positive node counts, and the published total.
Its success marker is `CONFIG3_A2_LEDGER_ONLY_AUDIT_PASS`.

## Archival limitation

The historical 47-row ledger is byte-stable (2,441 bytes, SHA-256
`bc6a5909d2de7b0cbc0e1a886a03c675b92419c8c4e553ad944e1a123dbc93ac`),
but it is not a complete raw execution certificate. The original 47
stdout/stderr/done/pid bundles are unavailable, and the row
`a2_separate/path_6_1` has no surviving observed exit receipt. The compact
prior-three evidence contains row-1 and row-7 partition artifacts but no
original A2 raw partition bundle.

The strict release above does not claim to recover those missing bytes. It
replaces the historical terminal claims with directly checked receipts for
the exact roster and a complete, separately checked fan-out for the guarded
parent. The retired direct-47 release schema is rejected.

## Trust boundary

- The ledger-only audit authenticates a CSV claim; it is not an independent
  raw execution proof.
- The certificate depends on the pinned C++ solver, its enumeration and
  canonicalization logic, the preserved executable/runtime, the Python
  verifier, the operating system, and the filesystem.
- The preserved executable and source are both hash-pinned, but no
  reproducible-build attestation proves that the executable was built from
  that source.
- The certificate establishes exhaustive `ZERO` coverage for Configuration 3.
  The formal reduction from order-18 Leech trees to the eight configurations
  is checked separately by the proof boundary.
