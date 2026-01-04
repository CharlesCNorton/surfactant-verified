#!/usr/bin/env python3
"""
Surfactant Decision REST API Server

Wraps the Coq-extracted OCaml decision logic in a REST API.
The OCaml code provides machine-checked correctness guarantees.

Usage:
    python server.py [--port 8080]

Endpoints:
    POST /recommend     - Get surfactant recommendation for a clinical state
    POST /dose          - Calculate dose for a given weight and product
    GET  /health        - Health check
    GET  /              - API documentation
"""

import subprocess
import json
import sys
import os
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs
import argparse
from datetime import datetime

# Path to the compiled OCaml CLI
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CLI_PATH = os.path.join(SCRIPT_DIR, "surfactant_cli.exe")
OCAMLRUN = "ocamlrun"  # Assumes ocamlrun is in PATH via opam

# Audit log
AUDIT_LOG = []

def log_request(endpoint, request_data, response_data):
    """Log requests for audit trail."""
    entry = {
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "endpoint": endpoint,
        "request": request_data,
        "response": response_data
    }
    AUDIT_LOG.append(entry)
    # Keep only last 1000 entries in memory
    if len(AUDIT_LOG) > 1000:
        AUDIT_LOG.pop(0)

def call_ocaml_cli(input_json):
    """Call the OCaml CLI with JSON input and return JSON output."""
    try:
        result = subprocess.run(
            [OCAMLRUN, CLI_PATH],
            input=json.dumps(input_json),
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode != 0:
            return {"error": f"CLI error: {result.stderr}"}
        return json.loads(result.stdout.strip())
    except subprocess.TimeoutExpired:
        return {"error": "CLI timeout"}
    except json.JSONDecodeError as e:
        return {"error": f"Invalid JSON from CLI: {e}"}
    except Exception as e:
        return {"error": str(e)}

def calculate_dose(weight_g, product):
    """Calculate dose using the same formula as the OCaml code."""
    dose_per_kg = {
        "survanta": 100,
        "curosurf": 200,
        "infasurf": 105
    }.get(product.lower(), 200)

    # Same rounding formula as Coq: (weight * dose_per_kg + 500) / 1000
    dose_mg = (weight_g * dose_per_kg + 500) // 1000
    return dose_mg

API_DOC = """
<!DOCTYPE html>
<html>
<head>
    <title>Surfactant Decision API</title>
    <style>
        body { font-family: monospace; max-width: 800px; margin: 40px auto; padding: 0 20px; }
        h1 { color: #333; }
        pre { background: #f4f4f4; padding: 15px; overflow-x: auto; }
        .endpoint { background: #e8f4e8; padding: 10px; margin: 10px 0; border-left: 4px solid #4a4; }
        .warning { background: #fff3cd; padding: 10px; border-left: 4px solid #ffc107; }
    </style>
</head>
<body>
    <h1>Surfactant Decision API</h1>
    <p class="warning">
        <strong>DISCLAIMER:</strong> This is decision SUPPORT software, not a medical device.
        All recommendations must be validated by qualified clinicians.
        The underlying logic is formally verified in Coq (machine-checked proofs).
    </p>

    <h2>Endpoints</h2>

    <div class="endpoint">
        <h3>POST /recommend</h3>
        <p>Get surfactant recommendation for a clinical state.</p>
        <pre>
Request:
{
    "patient": {
        "ga_weeks": 27,      // Gestational age weeks (22-42)
        "ga_days": 0,        // Gestational age days (0-6)
        "weight": 900,       // Birth weight in grams (200-6000)
        "age_hours": 6,      // Postnatal age in hours (0-168)
        "fio2": 45           // Current FiO2 percentage (21-100)
    },
    "signs": {
        "grunting": true,
        "retractions": true,
        "nasal_flaring": false,
        "cyanosis": false
    },
    "contraindications": {
        "cdh": false,                  // Congenital diaphragmatic hernia
        "lethal_anomaly": false,
        "pulmonary_hypoplasia": false,
        "pulmonary_hemorrhage": false,
        "pneumothorax": false
    },
    "cxr": {                          // Optional chest X-ray
        "ground_glass": true,
        "air_bronchograms": true,
        "low_volumes": true,
        "reticulogranular": false
    },
    "blood_gas": {
        "ph": 7350,           // pH * 1000 (e.g., 7.35 = 7350)
        "pco2": 40,           // mmHg
        "po2": 80             // mmHg
    },
    "minutes_since_birth": 360,
    "cpap_trial": {                   // Optional, required if support="cpap"
        "pressure": 7,
        "duration": 30,
        "fio2": 50
    },
    "support": "cpap",                // "room_air", "cpap", or "intubated"
    "product": "curosurf",            // "survanta", "curosurf", or "infasurf"
    "clinical_judgement": false       // Clinician override for imaging
}

Response:
{
    "result": "Indicated",    // "Indicated", "NotIndicated", "InvalidInput", "InvalidPatient"
    "product": "Curosurf",
    "dose_mg": 180,
    "weight_g": 900
}
        </pre>
    </div>

    <div class="endpoint">
        <h3>POST /dose</h3>
        <p>Calculate dose for a given weight and product.</p>
        <pre>
Request:
{
    "weight_g": 900,
    "product": "curosurf"
}

Response:
{
    "product": "curosurf",
    "weight_g": 900,
    "dose_mg": 180,
    "dose_per_kg": 200
}
        </pre>
    </div>

    <div class="endpoint">
        <h3>GET /health</h3>
        <p>Health check endpoint.</p>
        <pre>Response: {"status": "ok", "cli_available": true}</pre>
    </div>

    <div class="endpoint">
        <h3>GET /audit</h3>
        <p>Get recent audit log (last 100 entries).</p>
    </div>

    <h2>Clinical Guidelines</h2>
    <p>Based on European Consensus Guidelines on RDS Management (2022):</p>
    <ul>
        <li><strong>Prophylactic:</strong> GA &lt; 30 weeks, intubated for stabilization, within 15 min of birth</li>
        <li><strong>Rescue:</strong> FiO2 &gt; 30% on CPAP &ge; 6 cmH2O with clinical signs of RDS</li>
    </ul>

    <h2>Formal Verification</h2>
    <p>
        The decision logic is implemented in Coq with machine-checked proofs of:
    </p>
    <ul>
        <li>Contraindications always block recommendation</li>
        <li>Well infants (GA &ge; 30w, FiO2 &le; 30%) are never indicated</li>
        <li>Dose calculations are bounded for valid weights</li>
        <li>Boundary conditions (29+6w vs 30+0w) are correctly handled</li>
    </ul>
</body>
</html>
"""

class SurfactantHandler(BaseHTTPRequestHandler):
    def send_json(self, data, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode())

    def send_html(self, html, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "text/html")
        self.end_headers()
        self.wfile.write(html.encode())

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        path = urlparse(self.path).path

        if path == "/" or path == "/docs":
            self.send_html(API_DOC)

        elif path == "/health":
            cli_exists = os.path.exists(CLI_PATH)
            self.send_json({
                "status": "ok",
                "cli_available": cli_exists,
                "cli_path": CLI_PATH
            })

        elif path == "/audit":
            self.send_json(AUDIT_LOG[-100:])

        else:
            self.send_json({"error": "Not found"}, 404)

    def do_POST(self):
        path = urlparse(self.path).path
        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length).decode()

        try:
            request_data = json.loads(body) if body else {}
        except json.JSONDecodeError:
            self.send_json({"error": "Invalid JSON"}, 400)
            return

        if path == "/recommend":
            response = call_ocaml_cli(request_data)
            log_request("/recommend", request_data, response)
            self.send_json(response)

        elif path == "/dose":
            weight = request_data.get("weight_g", 1000)
            product = request_data.get("product", "curosurf")
            dose_per_kg = {"survanta": 100, "curosurf": 200, "infasurf": 105}.get(product.lower(), 200)
            dose = calculate_dose(weight, product)
            response = {
                "product": product,
                "weight_g": weight,
                "dose_mg": dose,
                "dose_per_kg": dose_per_kg
            }
            log_request("/dose", request_data, response)
            self.send_json(response)

        else:
            self.send_json({"error": "Not found"}, 404)

    def log_message(self, format, *args):
        # Quieter logging
        print(f"[{datetime.now().strftime('%H:%M:%S')}] {args[0]}")

def main():
    parser = argparse.ArgumentParser(description="Surfactant Decision REST API")
    parser.add_argument("--port", type=int, default=8080, help="Port to listen on")
    parser.add_argument("--host", default="127.0.0.1", help="Host to bind to")
    args = parser.parse_args()

    if not os.path.exists(CLI_PATH):
        print(f"ERROR: CLI not found at {CLI_PATH}")
        print("Please compile with: ocamlc str.cma surfactant_decision.mli surfactant_decision.ml surfactant_cli.ml -o surfactant_cli.exe")
        sys.exit(1)

    server = HTTPServer((args.host, args.port), SurfactantHandler)
    print(f"Surfactant Decision API Server")
    print(f"==============================")
    print(f"Listening on http://{args.host}:{args.port}")
    print(f"Documentation: http://{args.host}:{args.port}/docs")
    print(f"CLI path: {CLI_PATH}")
    print(f"Press Ctrl+C to stop")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down...")
        server.shutdown()

if __name__ == "__main__":
    main()
