# Third-party component inventory

The Apache-2.0 and CC-BY-4.0 grants described in the root `LICENSE` file apply
only to material the applicable rights holders have authority to license. They
do not override third-party terms.

## Retained Windows runtime files

The preserved evidence for Configurations 2, 3, and 8 contains three runtime
libraries beside the project search executables. The build record says
the executables were built with MSYS2 UCRT64 GNU g++ 14.2.0.

| File | Size (bytes) | SHA-256 |
|---|---:|---|
| `libgcc_s_seh-1.dll` | 155378 | `6c0a4c1fa1cdb36ba1d7be050a16f50edeaff12294178cdd25590ef3081b0e89` |
| `libstdc++-6.dll` | 2405564 | `bc95e3e3b3f83f03e9d05f7bb61c2bf42b4b15c2305b1130a0036d36f2148aa2` |
| `libwinpthread-1.dll` | 62284 | `0acbbb8652cdfce8cd4e9df34dc4f64539148e0de6ff1a2a6b2626808faddd36` |

They are located under:

```text
computation/evidence/production/
prior_three_configurations/work/a2_solver/
```

The corresponding upstream license and notice texts are included as
`LICENSES/GPL-3.0-or-later.txt`,
`LICENSES/GCC-Runtime-Library-Exception-3.1.txt`,
`LICENSES/Winpthreads.txt`, and `LICENSES/MinGW-w64-runtime.txt`. The presence
of a hash in this inventory is not itself a license grant.

All three retained project executables listed below dynamically import
`libgcc_s_seh-1.dll` and `libstdc++-6.dll`; those libraries in turn import
`libwinpthread-1.dll`. The executables also contain MSYS2/MinGW-w64 runtime
markers. Apache-2.0 covers the project-authored solver portions, but it does
not replace any applicable MinGW runtime, startup-code, or library terms.

## Project executables linked to that runtime

| File | Size (bytes) | SHA-256 |
|---|---:|---|
| `a2_topology_free_search_multicover.exe` | 355685 | `65bbaa57e5b462663b3656bc77499cc5956053f4137878c21072c99a327483f3` |
| `order18_topology_free_search_row1.exe` | 377255 | `5f50bec4d18947680ee170bf22af747d1e74ea203e34e305eae27768439b46ad` |
| `order18_topology_free_search.exe` | 360779 | `9f894f39efb71e9c8506e5c5b312289b1d3befe95c95b911df8613f2e24baffb` |

The corresponding project source snapshots are retained. The source-build
workflow in `scripts/recompute_prior_three_from_source.py` creates new
executables in a separate directory and never overwrites these historical
files.

## Build and proof dependencies

Lean and Lake dependencies are pinned by `lean-toolchain` and
`lake-manifest.json`. Generated `.lake` dependency trees are not part of the
Git-resident release. Each downloaded dependency remains under its own
upstream license.

Release packages should be assembled from Git-tracked files. The ignored local
`.lake` cache contains upstream packages
and vendored assets under their own Apache-2.0 or MIT terms; it is not covered
by the repository's project-authored-material defaults and must not be copied
without its accompanying upstream notices.

Python, PowerShell, Git, GNU g++, and operating-system facilities are external
prerequisites and are not relicensed by this repository.
