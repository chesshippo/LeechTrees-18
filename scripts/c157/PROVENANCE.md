# C157 source provenance

The eight files in `source/` are byte-for-byte copies of the production
prebuild snapshot retained in the full evidence asset at:

```text
computation/evidence/full/results/
20260817T211656Z_slurm376253/prebuild/provenance/
```

`SOURCE_MANIFEST.sha256` binds every copied byte.  The original production
compiler was GCC 12.2.0 and the original command was:

```text
g++ -O2 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  g001_remaining_shallow_pilot.cpp -o g001_remaining_shallow_pilot
```

The production executable had SHA-256
`bce4c2766fb9aedc942aaca7127eafac5c983e552d61266d882b87f2260f1147`.
That executable digest identifies the historical binary; a rebuild on another
toolchain is expected to have a different binary digest.  The public runner
records the compiler version and rebuilt binary digest and binds all results
to them.

The public runner uses the production `exact6`, validation-off arguments:

```text
--multi-edge-cover
--multi-edge-cover-no-hall
--multi-edge-cover-max-components 6
--multi-edge-cover-budget 100
--multi-edge-cover-no-exact-hall
--multi-edge-cover-exact-max-components 6
```

The frozen path partition and expected depth-12 frontier values come from
`terminal_plan_v1.json`, SHA-256
`b317a3b7cef71e11fea762ce5e70322f168e06c6e04b97293f066cb2e313bdae`.
They are treated as expected values, not as fresh results.  The runner invokes
the source-built shallow solver for every leaf and reconstructs every internal
fanout to check that the partition is prefix-free and exhaustive.
