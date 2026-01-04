#!/usr/bin/env python3
"""
Literature-Based Validation for Surfactant Decision Model

Runs the Coq-extracted OCaml decision logic against cases derived from
published clinical thresholds and validates concordance.

Usage:
    python validate_literature.py
"""

import json
import subprocess
import os
import sys
from datetime import datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CLI_PATH = os.path.join(SCRIPT_DIR, "surfactant_cli.exe")
CASES_PATH = os.path.join(SCRIPT_DIR, "literature_validation_cases.json")
OCAMLRUN = "ocamlrun"

def call_cli(case_data):
    """Call the OCaml CLI with case data."""
    # Build the request format expected by CLI with all required fields
    request = {
        "patient": case_data["patient"],
        "signs": case_data["signs"],
        "contraindications": case_data["contraindications"],
        "minutes_since_birth": case_data["minutes_since_birth"],
        "support": case_data["support"],
        "clinical_judgement": case_data.get("clinical_judgement", False),
        # Provide defaults for optional fields - CLI parser needs them
        "cxr": case_data.get("cxr", {
            "ground_glass": False,
            "air_bronchograms": False,
            "low_volumes": False,
            "reticulogranular": False
        }),
        "blood_gas": case_data.get("blood_gas", {
            "ph": 7350,
            "pco2": 40,
            "po2": 80
        }),
        "cpap_trial": case_data.get("cpap_trial", {
            "pressure": 0,
            "duration": 0,
            "fio2": 21
        }),
        "product": case_data.get("product", "curosurf")
    }

    try:
        # Try with opam exec first
        opam_path = r"C:\Users\cnort\AppData\Local\Microsoft\WinGet\Packages\OCaml.opam_Microsoft.Winget.Source_8wekyb3d8bbwe\opam.exe"
        if os.path.exists(opam_path):
            result = subprocess.run(
                [opam_path, "exec", "--switch=5.1.1", "--", "ocamlrun", CLI_PATH],
                input=json.dumps(request),
                capture_output=True,
                text=True,
                timeout=10
            )
        else:
            result = subprocess.run(
                [OCAMLRUN, CLI_PATH],
                input=json.dumps(request),
                capture_output=True,
                text=True,
                timeout=10
            )

        if result.returncode != 0:
            return {"error": result.stderr, "result": "Error"}

        return json.loads(result.stdout.strip())
    except Exception as e:
        return {"error": str(e), "result": "Error"}

def run_validation():
    """Run all validation cases and compute metrics."""

    # Check CLI exists
    if not os.path.exists(CLI_PATH):
        print(f"ERROR: CLI not found at {CLI_PATH}")
        print("Compile with: ocamlc str.cma surfactant_decision.mli surfactant_decision.ml surfactant_cli.ml -o surfactant_cli.exe")
        sys.exit(1)

    # Load cases
    with open(CASES_PATH) as f:
        data = json.load(f)

    cases = data["cases"]
    metadata = data["metadata"]

    print("=" * 70)
    print("LITERATURE-BASED VALIDATION")
    print("=" * 70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"Cases: {len(cases)}")
    print(f"Sources: {len(metadata['sources'])}")
    for src in metadata["sources"]:
        print(f"  - {src}")
    print("=" * 70)
    print()

    # Run cases
    results = []
    concordant = 0
    discordant = 0
    errors = 0

    for case in cases:
        case_id = case["id"]
        expected = case["expected"]
        description = case["description"]

        response = call_cli(case)
        actual = response.get("result", "Error")

        if actual == "Error":
            status = "ERROR"
            errors += 1
        elif actual == expected:
            status = "PASS"
            concordant += 1
        else:
            status = "FAIL"
            discordant += 1

        results.append({
            "id": case_id,
            "expected": expected,
            "actual": actual,
            "status": status,
            "description": description
        })

        # Print result
        status_symbol = {"PASS": "[OK]", "FAIL": "[XX]", "ERROR": "[??]"}[status]
        print(f"{status_symbol} {case_id}: {description[:50]}")
        if status != "PASS":
            print(f"       Expected: {expected}, Got: {actual}")
            if "error" in response:
                print(f"       Error: {response['error'][:60]}")

    # Summary
    total = len(cases)
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total cases:    {total}")
    print(f"Concordant:     {concordant} ({100*concordant/total:.1f}%)")
    print(f"Discordant:     {discordant} ({100*discordant/total:.1f}%)")
    print(f"Errors:         {errors}")
    print()

    if discordant == 0 and errors == 0:
        print("ALL CASES CONCORDANT WITH PUBLISHED THRESHOLDS")
        print()

        # Calculate formal metrics
        print("Concordance Metrics:")
        print(f"  Agreement rate: {100*concordant/total:.1f}%")
        print(f"  Kappa: N/A (no discordance)")
    else:
        print("DISCORDANT CASES REQUIRE REVIEW:")
        for r in results:
            if r["status"] != "PASS":
                print(f"  {r['id']}: expected {r['expected']}, got {r['actual']}")

    print("=" * 70)

    # Write results to file
    output = {
        "run_date": datetime.now().isoformat(),
        "summary": {
            "total": total,
            "concordant": concordant,
            "discordant": discordant,
            "errors": errors,
            "agreement_rate": concordant / total if total > 0 else 0
        },
        "results": results
    }

    output_path = os.path.join(SCRIPT_DIR, "VALIDATION_RESULTS.json")
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults written to: {output_path}")

    return concordant == total and errors == 0

if __name__ == "__main__":
    success = run_validation()
    sys.exit(0 if success else 1)
