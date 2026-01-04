#!/usr/bin/env python3
"""Run SPIN verification on the surfactant model."""
import subprocess
import os
import re

WORKDIR = os.path.dirname(os.path.abspath(__file__))
PML_IN = os.path.join(WORKDIR, 'surfactant.pml')
PML_OUT = os.path.join(WORKDIR, 'surfactant_pp.pml')
SPIN = r'C:\Users\cnort\spin649.exe'

def preprocess():
    """Manually preprocess Promela file."""
    with open(PML_IN, 'r') as f:
        content = f.read()

    # Handle line continuations
    content = re.sub(r'\\\n', ' ', content)

    # Extract and apply #define macros
    defines = {}
    lines = []
    for line in content.split('\n'):
        m = re.match(r'#define\s+(\w+)\s+(.+)', line)
        if m:
            name = m.group(1)
            val = m.group(2).split('/*')[0].strip()
            defines[name] = val
        else:
            lines.append(line)

    content = '\n'.join(lines)

    # Apply substitutions (longest names first to avoid partial matches)
    for name in sorted(defines.keys(), key=len, reverse=True):
        # Use word boundaries
        pattern = r'\b' + re.escape(name) + r'\b'
        content = re.sub(pattern, defines[name], content)

    with open(PML_OUT, 'w') as f:
        f.write(content)

    return len(defines)

def run_spin():
    """Run SPIN verification."""
    print("=" * 60)
    print("SPIN Verification of Surfactant Model")
    print("=" * 60)

    # Preprocess
    print("\n[1] Preprocessing...")
    n = preprocess()
    print(f"  Expanded {n} macros")
    print(f"  Output: {PML_OUT}")

    # Generate verifier
    print("\n[2] Generating verifier (spin -n -a)...")
    result = subprocess.run([SPIN, '-n', '-a', PML_OUT],
                          capture_output=True, text=True, cwd=WORKDIR)
    print(f"  Return code: {result.returncode}")
    if result.stderr:
        for line in result.stderr.strip().split('\n')[:10]:
            print(f"  {line}")

    # Check generated files
    print("\n[3] Generated files:")
    for f in ['pan.c', 'pan.h', 'pan.m', 'pan.t', 'pan.b']:
        path = os.path.join(WORKDIR, f)
        if os.path.exists(path):
            print(f"  {f}: {os.path.getsize(path)} bytes")

    # Run simulation
    print("\n[4] Simulation (300 steps)...")
    result = subprocess.run([SPIN, '-n', '-p', '-u300', PML_OUT],
                          capture_output=True, text=True, cwd=WORKDIR)
    if result.stdout:
        lines = result.stdout.strip().split('\n')
        print(f"  {len(lines)} output lines")
        print("  Last 20 lines:")
        for line in lines[-20:]:
            print(f"    {line}")
    if result.stderr:
        print(f"  Errors: {result.stderr[:300]}")

    print("\n" + "=" * 60)
    print("Note: Full LTL verification requires gcc to compile pan.c")
    print("=" * 60)

if __name__ == '__main__':
    run_spin()
