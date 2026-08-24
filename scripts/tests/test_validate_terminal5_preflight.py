#!/usr/bin/env python3
"""Unit tests for the release-side Terminal5 fail-closed preflight."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "validate_terminal5_preflight.py"
SPEC = importlib.util.spec_from_file_location("validate_terminal5_preflight", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {SCRIPT}")
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class SelectorReachabilityTests(unittest.TestCase):
    def test_valid_path_is_accepted(self) -> None:
        MODULE.validate_selector_reached(
            [5, 3, 14, 21, 29, 18],
            {
                "root_valid": "6",
                "child_max": "3:8,4:4,5:15,6:22,7:30,8:39,",
            },
            "valid",
        )

    def test_known_invalid_ordinal_999_false_zero_is_rejected(self) -> None:
        # The immutable solver returned status=ZERO, root_valid=0 for this
        # malformed selector.  The release preflight must fail closed.
        with self.assertRaisesRegex(MODULE.PreflightError, "did not reach"):
            MODULE.validate_selector_reached(
                [999],
                {"status": "ZERO", "root_valid": "0", "child_max": "3:8,"},
                "ordinal-999 regression",
            )

    def test_selector_equal_to_child_count_is_rejected(self) -> None:
        with self.assertRaisesRegex(MODULE.PreflightError, "outside child_max"):
            MODULE.validate_selector_reached(
                [5, 4],
                {"root_valid": "6", "child_max": "3:8,4:4,"},
                "out-of-range",
            )

    def test_absent_selected_depth_is_rejected(self) -> None:
        with self.assertRaisesRegex(MODULE.PreflightError, "did not record selected depth"):
            MODULE.validate_selector_reached(
                [0, 0],
                {"root_valid": "1", "child_max": "3:1,"},
                "missing-depth",
            )

    def test_duplicate_child_max_depth_is_rejected(self) -> None:
        with self.assertRaisesRegex(MODULE.PreflightError, "duplicate depth"):
            MODULE.validate_selector_reached(
                [0],
                {"root_valid": "1", "child_max": "3:1,3:2,"},
                "duplicate-depth",
            )

    def test_noncanonical_numeric_field_is_rejected(self) -> None:
        with self.assertRaisesRegex(MODULE.PreflightError, "canonical"):
            MODULE.validate_selector_reached(
                [0],
                {"root_valid": "00", "child_max": "3:1,"},
                "numeric",
            )


class OutputReceiptTests(unittest.TestCase):
    def test_output_creation_refuses_existing_path_without_changing_it(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "receipt.json"
            target.write_bytes(b"sentinel\n")
            with self.assertRaisesRegex(MODULE.PreflightError, "refusing/cannot create"):
                MODULE.write_new(target, b"replacement\n")
            self.assertEqual(target.read_bytes(), b"sentinel\n")

    def test_output_creation_writes_exact_canonical_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "receipt.json"
            expected = MODULE.canonical_json_bytes(
                {"status": "PASS", "schema": MODULE.RECEIPT_SCHEMA}
            )
            MODULE.write_new(target, expected)
            self.assertEqual(target.read_bytes(), expected)


if __name__ == "__main__":
    unittest.main()
