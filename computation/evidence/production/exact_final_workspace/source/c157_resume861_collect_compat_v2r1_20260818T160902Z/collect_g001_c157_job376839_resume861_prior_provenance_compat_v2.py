#!/usr/bin/env python3
"""Narrow collection-only compatibility launcher for resume861 job377219.

The frozen V2 continuation computation, its external freeze, and its collector
remain byte-for-byte unchanged.  This launcher corrects one collection-time
source-root assumption: the frozen job376839 verifier is loaded from the exact
prior provenance closure that it originally recorded, rather than from the
newer continuation source directory.

Nothing here launches or reruns scientific work.  Publication is still done by
the frozen V2 collector with its private full verification and atomic
no-replace commit.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import sys
from types import ModuleType
from typing import Any, Callable, Dict, Mapping, Optional, Sequence, Set, Tuple


SCHEMA = "g001-c157-job376839-resume861-prior-provenance-compat-v2"
FROZEN_COLLECTOR_NAME = (
    "collect_g001_c157_job376839_resumable_continuation_v1.py")
FROZEN_MERGE_NAME = (
    "verify_g001_c157_job376839_resumable_continuation_merge_v1.py")
FROZEN_FREEZE_NAME = (
    "g001_c157_job376839_resumable_continuation_external_freeze_v1.json")
FROZEN_CHECKSUM_NAME = (
    "G001_C157_JOB376839_RESUMABLE_CONTINUATION_V1_SHA256SUMS.txt")
FROZEN_FREEZE_SHA256 = (
    "46344014378627646179027cbd9cc5a5f64b6927b40fe17635343ea2c1d2a364")
FROZEN_CHECKSUM_SHA256 = (
    "23183b20ef5e114576cbe8ab003a9bcbd9466a371420ead6cd94a50ea62d01b6")
FROZEN_COLLECTOR_SHA256 = (
    "398f11b26d0cd0d143927ac127a4265bd7a72757cef9bcff260a604dce075092")
FROZEN_MERGE_SHA256 = (
    "131363a2549abe254a8c169b4e19511443be197653725f123da0ac1787d964b5")
FROZEN_SOURCE_EXACT_COUNT = 22

# These hashes were derived from, and are independently checkable against,
# SHA256 3c9a55b4910af2a25627214f5f1eef28b3d85ac5b0bf95a397b0cd3c68d0f9b1
# (AMD_G001_C157_ADAPTIVE_MATRIX_V1_RAW_SLURM376839.tar.gz).  All 16 prior
# shards must contain exactly this same nine-file provenance closure.
PRIOR_RAW_ARCHIVE_SHA256 = (
    "3c9a55b4910af2a25627214f5f1eef28b3d85ac5b0bf95a397b0cd3c68d0f9b1")
PRIOR_PROVENANCE_FILES: Mapping[str, str] = {
    "g001_c157_external_freeze_manifest_v1.json":
        "96168e78cb30f51f96e78a16983716a9f22cccaabc5c185bd5cd8b4e5f5afeaf",
    "g001_configs_1_5_6_7_adaptive_common_v0.py":
        "39dce6e656b0203c9189e6d20ede9e088fa2cc410e347e1eda8abbbe9c8578b5",
    "g001_configs_1_5_6_7_adaptive_common_v1.py":
        "e2459e9cba38b11b4a709a1cfa1e85a13999ac1579fc143b9f9da62ded5fd7e1",
    "run_g001_configs_1_5_6_7_adaptive_shard_v1.py":
        "f15eda92878fb63a51cb5ec5720aa7ad5809085a0b64a7a37cea4ff8dd24054b",
    "run_g001_remaining_shallow_benchmark.py":
        "4d712785e237387b6d005c4c56476c61de63305faffbfddf235a88dea1acb174",
    "run_g001_remaining_shallow_benchmark_engine_v1.py":
        "cfe640e164b2e1a897ce51558fee951376d0691917ad5186b4aa2e4ca7122493",
    "verify_g001_configs_1_5_6_7_adaptive_shards_v1.py":
        "d2758766ad17db9da4c36d9199b7fee65c372b7533f0a98b113bbcb68aff8828",
    "verify_g001_configs_1_5_6_7_depth12_plan_v1.py":
        "65cafa504b6debe35f3c265ccf6f11143c3c6e886250665370d012be817a6718",
    "verify_g001_remaining_shallow_pilot.py":
        "1ed169b8409962b9fd641b013daab34c7eb1456ba82b6853e3667542e94eb9fb",
}

FROZEN_IMPORT_NAMES = (
    "g001_c157_job376839_resumable_continuation_common_v1",
    "g001_c157_job376839_resumable_continuation_atomic_v1",
    "make_g001_c157_job376839_resumable_continuation_freeze_v1",
    "verify_g001_c157_job376839_resumable_continuation_external_freeze_v1",
    "verify_g001_c157_job376839_resumable_continuation_merge_v1",
    "verify_g001_c157_job376839_resumable_continuation_plan_v1",
    "verify_g001_c157_job376839_resumable_continuation_shards_v1",
    "g001_configs_1_5_6_7_adaptive_common_v0",
    "g001_configs_1_5_6_7_adaptive_common_v1",
    "verify_g001_configs_1_5_6_7_adaptive_shards_v1",
    "verify_g001_remaining_shallow_pilot",
)
PRIOR_IMPORT_NAMES = (
    "g001_configs_1_5_6_7_adaptive_common_v0",
    "g001_configs_1_5_6_7_adaptive_common_v1",
    "verify_g001_remaining_shallow_pilot",
)


class CompatibilityError(RuntimeError):
    """Raised before publication when the compatibility binding is not exact."""


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def read_regular(path: Path, label: str) -> bytes:
    path = Path(path)
    try:
        info = path.lstat()
    except OSError as error:
        raise CompatibilityError(label + " is missing") from error
    if (stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode) or
            info.st_nlink != 1):
        raise CompatibilityError(label + " is not a single-link regular file")
    return path.read_bytes()


def regular_directory(path: Path, label: str) -> Path:
    path = Path(os.path.abspath(os.fspath(path)))
    try:
        info = path.lstat()
    except OSError as error:
        raise CompatibilityError(label + " is missing") from error
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise CompatibilityError(label + " is not a non-symlink directory")
    return path


def strict_object(raw: bytes, label: str) -> Dict[str, Any]:
    def pairs(pairs_value: Sequence[Tuple[str, Any]]) -> Dict[str, Any]:
        result: Dict[str, Any] = {}
        for key, value in pairs_value:
            if key in result:
                raise CompatibilityError("duplicate JSON key in " + label)
            result[key] = value
        return result
    try:
        value = json.loads(
            raw.decode("utf-8", errors="strict"), object_pairs_hook=pairs,
            parse_constant=lambda token: (_ for _ in ()).throw(
                CompatibilityError("non-finite JSON in " + label)))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CompatibilityError(label + " is not strict UTF-8 JSON") from error
    if not isinstance(value, dict):
        raise CompatibilityError(label + " is not a JSON object")
    return value


def option_value(argv: Sequence[str], option: str) -> Optional[str]:
    found = []
    index = 0
    while index < len(argv):
        item = argv[index]
        if item == option:
            if index + 1 >= len(argv):
                raise CompatibilityError(option + " lacks a value")
            found.append(argv[index + 1])
            index += 2
            continue
        if item.startswith(option + "="):
            found.append(item[len(option) + 1:])
        index += 1
    if len(found) > 1:
        raise CompatibilityError("duplicate " + option)
    if found and not found[0]:
        raise CompatibilityError(option + " has an empty value")
    return found[0] if found else None


def _flat_exact_set(root: Path, expected: Set[str], label: str) -> None:
    observed = set()
    for item in root.iterdir():
        info = item.lstat()
        if (stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode) or
                info.st_nlink != 1):
            raise CompatibilityError(label + " contains a non-regular entry")
        observed.add(item.name)
    if observed != expected:
        raise CompatibilityError(label + " exact set mismatch")


def bootstrap_frozen_source(argv: Sequence[str]) -> Tuple[Path, Path]:
    """Bind the frozen V2 bytes before importing any V2 Python module."""
    verify_package = option_value(argv, "--verify-package")
    supplied_source = option_value(argv, "--source-dir")
    supplied_freeze = option_value(argv, "--external-freeze")
    if verify_package is not None:
        if supplied_source is not None or supplied_freeze is not None:
            raise CompatibilityError(
                "package verification cannot supply a live source/freeze")
        package = regular_directory(Path(verify_package), "collected package")
        source_dir = regular_directory(
            package / "provenance" / "distribution",
            "packaged frozen V2 distribution")
        freeze_path = package / "provenance" / FROZEN_FREEZE_NAME
        live_layout = False
    else:
        if supplied_source is None or supplied_freeze is None:
            raise CompatibilityError(
                "collection requires --source-dir and --external-freeze")
        source_dir = regular_directory(
            Path(supplied_source), "live frozen V2 source")
        freeze_path = Path(os.path.abspath(supplied_freeze))
        live_layout = True
    freeze_raw = read_regular(freeze_path, "frozen V2 external freeze")
    if sha256_bytes(freeze_raw) != FROZEN_FREEZE_SHA256:
        raise CompatibilityError("frozen V2 external-freeze digest mismatch")
    freeze = strict_object(freeze_raw, "frozen V2 external freeze")
    distribution = freeze.get("distribution_files")
    if (not isinstance(distribution, dict) or
            not all(isinstance(name, str) and isinstance(digest, str)
                    for name, digest in distribution.items()) or
            distribution.get(FROZEN_COLLECTOR_NAME) !=
            FROZEN_COLLECTOR_SHA256 or
            distribution.get(FROZEN_MERGE_NAME) != FROZEN_MERGE_SHA256):
        raise CompatibilityError("frozen V2 distribution binding mismatch")
    expected = set(distribution)
    if live_layout:
        expected.update({FROZEN_FREEZE_NAME, FROZEN_CHECKSUM_NAME})
        if len(expected) != FROZEN_SOURCE_EXACT_COUNT:
            raise CompatibilityError("frozen V2 live exact-count mismatch")
        checksum = read_regular(
            source_dir / FROZEN_CHECKSUM_NAME, "frozen V2 checksum")
        if sha256_bytes(checksum) != FROZEN_CHECKSUM_SHA256:
            raise CompatibilityError("frozen V2 checksum digest mismatch")
        if (source_dir / FROZEN_FREEZE_NAME).resolve() != freeze_path.resolve():
            raise CompatibilityError("live freeze is not inside frozen V2 source")
    _flat_exact_set(source_dir, expected, "frozen V2 source")
    for name, digest in distribution.items():
        if sha256_bytes(read_regular(
                source_dir / name, "frozen V2 distribution file")) != digest:
            raise CompatibilityError("frozen V2 source digest mismatch for " + name)
    return source_dir, freeze_path


def prior_provenance_closure(source_dir: Path) -> Dict[str, str]:
    source_dir = regular_directory(source_dir, "prior provenance directory")
    _flat_exact_set(source_dir, set(PRIOR_PROVENANCE_FILES),
                    "prior provenance directory")
    observed: Dict[str, str] = {}
    for name in sorted(PRIOR_PROVENANCE_FILES):
        digest = sha256_bytes(read_regular(
            source_dir / name, "prior provenance file"))
        if digest != PRIOR_PROVENANCE_FILES[name]:
            raise CompatibilityError(
                "archived prior provenance digest mismatch for " + name)
        observed[name] = digest
    return observed


def canonical_prior_source(prior_matrix_root: Path) -> Path:
    """Require one identical archived provenance closure in all 16 shards."""
    root = regular_directory(prior_matrix_root, "prior matrix root")
    canonical = root / "shard_00" / "provenance"
    expected = prior_provenance_closure(canonical)
    for index in range(1, 16):
        source = root / "shard_{:02d}".format(index) / "provenance"
        if prior_provenance_closure(source) != expected:
            raise CompatibilityError(
                "prior provenance closure differs in shard_{:02d}".format(index))
    return canonical


def _module_path(module: ModuleType, label: str) -> Path:
    name = getattr(module, "__file__", None)
    if not isinstance(name, str):
        raise CompatibilityError(label + " lacks a source path")
    return Path(name).resolve()


def isolated_prior_loader(
        original_loader: Callable[[Path], ModuleType], source_dir: Path) -> ModuleType:
    """Load the old verifier and dependencies without module-name collision."""
    source_dir = regular_directory(source_dir, "canonical prior source")
    before = prior_provenance_closure(source_dir)
    saved_modules = {name: sys.modules.get(name) for name in PRIOR_IMPORT_NAMES}
    saved_path = list(sys.path)
    saved_dont_write = sys.dont_write_bytecode
    try:
        for name in PRIOR_IMPORT_NAMES:
            sys.modules.pop(name, None)
        sys.path.insert(0, str(source_dir))
        sys.dont_write_bytecode = True
        module = original_loader(source_dir)
        expected_paths = {
            _module_path(module.common, "prior common"):
                "g001_configs_1_5_6_7_adaptive_common_v1.py",
            _module_path(module.common._v0, "prior legacy common"):
                "g001_configs_1_5_6_7_adaptive_common_v0.py",
            _module_path(module.base, "prior base verifier"):
                "verify_g001_remaining_shallow_pilot.py",
            _module_path(module, "prior verifier"):
                "verify_g001_configs_1_5_6_7_adaptive_shards_v1.py",
        }
        for path, name in expected_paths.items():
            if path != (source_dir / name).resolve():
                raise CompatibilityError(
                    "isolated prior verifier imported outside archived provenance")
    finally:
        sys.path[:] = saved_path
        sys.dont_write_bytecode = saved_dont_write
        for name, previous in saved_modules.items():
            if previous is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = previous
    if prior_provenance_closure(source_dir) != before:
        raise CompatibilityError("prior provenance changed during isolated load")
    return module


def make_compat_verify_merge(
        original_verify_merge: Callable[..., Dict[str, Any]]) -> Callable[..., Dict[str, Any]]:
    def verify_merge(
            plan_path: Path, _continuation_source_dir: Path,
            prior_matrix_root: Path, continuation_matrix_root: Path,
            prior_raw_archive: Path, prior_compact_archive: Path,
            prior_collected_package: Path, require_complete: bool) -> Dict[str, Any]:
        canonical = canonical_prior_source(prior_matrix_root)
        result = original_verify_merge(
            plan_path, canonical, prior_matrix_root, continuation_matrix_root,
            prior_raw_archive, prior_compact_archive,
            prior_collected_package, require_complete)
        # Catch any unexpected mutation or source-root drift before the caller
        # can stage or publish a package.
        if canonical_prior_source(prior_matrix_root) != canonical:
            raise CompatibilityError("canonical prior provenance root drifted")
        return result
    return verify_merge


def load_frozen_collector(source_dir: Path) -> ModuleType:
    source_dir = regular_directory(source_dir, "frozen V2 source")
    collector_path = source_dir / FROZEN_COLLECTOR_NAME
    if sha256_bytes(read_regular(
            collector_path, "frozen V2 collector")) != FROZEN_COLLECTOR_SHA256:
        raise CompatibilityError("frozen V2 collector digest mismatch")
    saved_modules = {name: sys.modules.get(name) for name in FROZEN_IMPORT_NAMES}
    saved_path = list(sys.path)
    saved_dont_write = sys.dont_write_bytecode
    try:
        for name in FROZEN_IMPORT_NAMES:
            sys.modules.pop(name, None)
        sys.path.insert(0, str(source_dir))
        sys.dont_write_bytecode = True
        specification = importlib.util.spec_from_file_location(
            "_g001_c157_resume861_frozen_v2_collector", str(collector_path))
        if specification is None or specification.loader is None:
            raise CompatibilityError("cannot load frozen V2 collector")
        collector = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(collector)
        required = ("main", "merge", "common", "external", "maker", "strict")
        if any(not hasattr(collector, name) for name in required):
            raise CompatibilityError("frozen V2 collector API mismatch")
        if (_module_path(collector, "frozen V2 collector") !=
                collector_path.resolve() or
                _module_path(collector.merge, "frozen V2 merge") !=
                (source_dir / FROZEN_MERGE_NAME).resolve()):
            raise CompatibilityError("frozen V2 collector imported wrong module")
    finally:
        sys.path[:] = saved_path
        sys.dont_write_bytecode = saved_dont_write
        for name, previous in saved_modules.items():
            if previous is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = previous
    return collector


def install_compatibility(collector: ModuleType) -> None:
    frozen_merge = collector.merge
    if getattr(frozen_merge, "_resume861_prior_compat_v2_installed", False):
        raise CompatibilityError("compatibility layer already installed")
    original_loader = frozen_merge.load_pristine_prior_verifier
    original_verify_merge = frozen_merge.verify_merge

    def loader(source_dir: Path) -> ModuleType:
        return isolated_prior_loader(original_loader, source_dir)

    frozen_merge.load_pristine_prior_verifier = loader
    frozen_merge.verify_merge = make_compat_verify_merge(original_verify_merge)
    frozen_merge._resume861_prior_compat_v2_installed = True


def main(argv: Optional[Sequence[str]] = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    try:
        source_dir, _freeze_path = bootstrap_frozen_source(arguments)
        collector = load_frozen_collector(source_dir)
        install_compatibility(collector)
        return int(collector.main(arguments))
    except (CompatibilityError, OSError, ValueError, KeyError) as error:
        print("G001_C157_RESUME861_PRIOR_PROVENANCE_COMPAT_V2_FAILED: {}".format(
            error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
