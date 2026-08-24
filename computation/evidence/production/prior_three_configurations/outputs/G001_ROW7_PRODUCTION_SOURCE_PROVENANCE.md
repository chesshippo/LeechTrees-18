# G001 row-7 production source provenance

Date: 2026-08-16

The executable used by every certified row-7 production partition is

```text
9F894F39EFB71E9C8506E5C5B312289B1D3BEFE95C95B911DF8613F2E24BAFFB
work/a2_solver/order18_topology_free_search.exe
```

Its exact source snapshot has been recovered as

```text
47183D7B30132BB5E6CC5039BC592EB90B900E8124C08DF6ED31EA61B689E2CC
work/a2_solver/order18_topology_free_search_production_snapshot.cpp
```

The snapshot is 41,741 bytes. Preserved provenance records the following
order of operations:

1. the row-7 mode was added to the frozen A2 source;
2. that intermediate source had SHA-256 `C04279B699D4B261A25CE21143937AE7EBE1F053325B9C4B084E25B99129FE49`;
3. the 18-byte text `--root-branch I` was added to the help message only;
4. the production executable was then compiled.

Consequently `C04279...` is a pre-production intermediate, while
`47183D7...` is the source compiled for the production run.

## Rebuild comparison

The recovered snapshot was rebuilt from `work/a2_solver` with GNU g++ using

```text
g++ -O2 -std=c++20 -Wall -Wextra -Wpedantic
```

and the same executable basename.  The rebuilt and production executables
both had size 360,779 bytes.  They differed at only six PE-header bytes:
three timestamp bytes at offsets 136--138 and three checksum bytes at offsets
216--218.  All other 360,773 bytes were identical.  This is the expected
non-semantic variation from rebuilding a PE executable at a different time.

## Behavioral regression comparison

The rebuilt source passed all of the following checks:

- `--help`, exit 0;
- row-7 three-edge seed: one frontier state with MEX 7;
- row-7 four-edge fan-out: five children, `root_valid=5`, MEX distribution
  `8:3,9:2`;
- the root-0 shallow selector;
- small-order topology counts `1,1,2,0,1` for orders 2 through 6; and
- the established A2 attached partition `--branch-path 1,1`, which returned
  `ZERO` with exactly 32,841 nodes.

On every shallow comparison, the rebuilt and frozen production executables
emitted byte-identical solver output.  The A2 regression output also matched
the frozen A2 executable.
