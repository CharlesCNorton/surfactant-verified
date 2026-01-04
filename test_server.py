#!/usr/bin/env python3
"""
Test suite for Surfactant Decision REST API Server

Tests the server.py endpoints and helper functions.
Run with: pytest test_server.py -v
"""

import pytest
import json
import sys
import os

# Add current directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from server import calculate_dose, log_request, AUDIT_LOG, API_DOC


class TestDoseCalculation:
    """Test the calculate_dose function matches Coq extraction."""

    def test_survanta_1000g(self):
        """Survanta: 100 mg/kg -> 1000g = 100mg"""
        assert calculate_dose(1000, "survanta") == 100

    def test_survanta_900g(self):
        """Survanta: 100 mg/kg -> 900g = 90mg"""
        assert calculate_dose(900, "survanta") == 90

    def test_curosurf_1000g(self):
        """Curosurf: 200 mg/kg -> 1000g = 200mg"""
        assert calculate_dose(1000, "curosurf") == 200

    def test_curosurf_900g(self):
        """Curosurf: 200 mg/kg -> 900g = 180mg"""
        assert calculate_dose(900, "curosurf") == 180

    def test_infasurf_1000g(self):
        """Infasurf: 105 mg/kg -> 1000g = 105mg"""
        assert calculate_dose(1000, "infasurf") == 105

    def test_infasurf_800g(self):
        """Infasurf: 105 mg/kg -> 800g = 84mg"""
        assert calculate_dose(800, "infasurf") == 84

    def test_case_insensitive(self):
        """Product names should be case-insensitive."""
        assert calculate_dose(1000, "SURVANTA") == 100
        assert calculate_dose(1000, "Curosurf") == 200
        assert calculate_dose(1000, "INFASURF") == 105

    def test_unknown_product_defaults_to_curosurf(self):
        """Unknown products default to Curosurf dose (200 mg/kg)."""
        assert calculate_dose(1000, "unknown") == 200

    def test_rounding_formula(self):
        """Verify rounding: (weight * dose_per_kg + 500) / 1000"""
        # 849g * 100 + 500 = 85400 // 1000 = 85
        assert calculate_dose(849, "survanta") == 85
        # 850g * 100 + 500 = 85500 // 1000 = 85
        assert calculate_dose(850, "survanta") == 85
        # 855g * 100 + 500 = 86000 // 1000 = 86
        assert calculate_dose(855, "survanta") == 86

    def test_minimum_weight(self):
        """Minimum valid weight (200g) produces positive dose."""
        assert calculate_dose(200, "survanta") == 20
        assert calculate_dose(200, "curosurf") == 40
        assert calculate_dose(200, "infasurf") == 21

    def test_maximum_weight(self):
        """Maximum valid weight (6000g) produces bounded dose."""
        assert calculate_dose(6000, "survanta") == 600
        assert calculate_dose(6000, "curosurf") == 1200
        assert calculate_dose(6000, "infasurf") == 630

    def test_preterm_weights(self):
        """Common preterm weights."""
        # 500g ELBW
        assert calculate_dose(500, "curosurf") == 100
        # 750g
        assert calculate_dose(750, "curosurf") == 150
        # 1500g
        assert calculate_dose(1500, "curosurf") == 300


class TestAuditLogging:
    """Test the audit logging functionality."""

    def setup_method(self):
        """Clear audit log before each test."""
        AUDIT_LOG.clear()

    def test_log_request_adds_entry(self):
        """log_request should add entry to AUDIT_LOG."""
        log_request("/test", {"input": 1}, {"output": 2})
        assert len(AUDIT_LOG) == 1
        assert AUDIT_LOG[0]["endpoint"] == "/test"
        assert AUDIT_LOG[0]["request"] == {"input": 1}
        assert AUDIT_LOG[0]["response"] == {"output": 2}

    def test_log_has_timestamp(self):
        """Log entries should have ISO timestamp."""
        log_request("/test", {}, {})
        assert "timestamp" in AUDIT_LOG[0]
        assert AUDIT_LOG[0]["timestamp"].endswith("Z")

    def test_log_max_entries(self):
        """Audit log should cap at 1000 entries."""
        for i in range(1050):
            log_request(f"/test{i}", {}, {})
        assert len(AUDIT_LOG) == 1000
        # First entries should be removed
        assert AUDIT_LOG[0]["endpoint"] == "/test50"


class TestAPIDocumentation:
    """Test the API documentation."""

    def test_api_doc_exists(self):
        """API_DOC should be a non-empty string."""
        assert isinstance(API_DOC, str)
        assert len(API_DOC) > 100

    def test_api_doc_contains_endpoints(self):
        """API_DOC should document all endpoints."""
        assert "/recommend" in API_DOC
        assert "/dose" in API_DOC
        assert "/health" in API_DOC
        assert "/audit" in API_DOC

    def test_api_doc_contains_disclaimer(self):
        """API_DOC should contain medical disclaimer."""
        assert "DISCLAIMER" in API_DOC
        assert "decision SUPPORT" in API_DOC

    def test_api_doc_mentions_coq(self):
        """API_DOC should mention Coq verification."""
        assert "Coq" in API_DOC
        assert "machine-checked" in API_DOC


class TestDoseConsistencyWithOCaml:
    """
    Test that Python dose calculation matches OCaml extraction.
    These are the same test cases from test_surfactant.ml.
    """

    def test_survanta_doses(self):
        """Match OCaml test_dose_calculation for Survanta."""
        assert calculate_dose(1000, "survanta") == 100  # 100mg
        assert calculate_dose(800, "survanta") == 80    # 80mg
        assert calculate_dose(849, "survanta") == 85    # 85mg (rounded)

    def test_curosurf_doses(self):
        """Match OCaml test_dose_calculation for Curosurf."""
        assert calculate_dose(1000, "curosurf") == 200  # 200mg
        assert calculate_dose(800, "curosurf") == 160   # 160mg

    def test_infasurf_doses(self):
        """Match OCaml test_dose_calculation for Infasurf."""
        assert calculate_dose(1000, "infasurf") == 105  # 105mg
        assert calculate_dose(800, "infasurf") == 84    # 84mg


class TestBoundaryConditions:
    """Test boundary conditions for dose calculations."""

    def test_dose_always_positive(self):
        """Dose should always be positive for valid weights."""
        for weight in range(200, 6001, 100):
            for product in ["survanta", "curosurf", "infasurf"]:
                dose = calculate_dose(weight, product)
                assert dose > 0, f"Dose should be positive for {weight}g {product}"

    def test_dose_monotonic(self):
        """Higher weight should give higher or equal dose."""
        for product in ["survanta", "curosurf", "infasurf"]:
            prev_dose = 0
            for weight in range(200, 6001, 10):
                dose = calculate_dose(weight, product)
                assert dose >= prev_dose, f"Dose should be monotonic for {product}"
                prev_dose = dose


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
