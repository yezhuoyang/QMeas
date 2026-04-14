"""Scan QASMBench for the set of gates every program uses, and classify
each program by what the QMeas compiler needs to support it.

Output: for each size bucket (small / medium / large), a table showing:
  - program name and qubit count
  - number of gates
  - which gate classes appear:
      [C]  pure Clifford subset of our compiler    ({h, s, sdg, cx, cz, swap, x, y, z})
      [T]  uses T or T_dagger  (magic-state injection path)
      [R]  uses arbitrary rotations (rx, ry, rz, u1, u2, u3, ...)
      [>2] uses 3+-qubit gates (ccx, ccz, cswap, ...)
  - a yes/no for "our compiler can handle this today"

This tells us exactly what fraction of QASMBench the current QMeas
compiler covers and what extensions are needed.
"""

from __future__ import annotations
import os
import sys
from collections import Counter

try:
    from qiskit import QuantumCircuit
except ImportError:
    print("qiskit not installed. Install with: pip install qiskit")
    sys.exit(1)


QASMBENCH_ROOT = r"C:\Users\yezhu\Documents\MeasureLanguage\QASMBench"

# Gate classification
CLIFFORD_1Q   = {"h", "s", "sdg", "x", "y", "z", "id"}
CLIFFORD_2Q   = {"cx", "cz", "swap", "iswap"}
T_GATES       = {"t", "tdg"}
ROTATIONS_1Q  = {"rx", "ry", "rz", "u1", "u2", "u3", "u", "p", "r"}
ROTATIONS_2Q  = {"crx", "cry", "crz", "cu1", "cu3", "cu", "cp", "rxx", "ryy", "rzz", "rzx"}
THREE_PLUS    = {"ccx", "ccz", "cswap", "c3x", "c4x", "mcx", "toffoli", "fredkin"}
OTHER         = {"measure", "reset", "barrier"}

SUPPORTED_BY_QMEAS_COMPILER_TODAY = CLIFFORD_1Q | CLIFFORD_2Q | T_GATES
# Everything else currently needs either decomposition (`transpile`) or
# future extension.


def classify_circuit(qc: QuantumCircuit) -> dict:
    """Return a dict of gate-class flags and a counter of individual gates."""
    gates = Counter()
    for inst in qc.data:
        name = inst.operation.name.lower()
        gates[name] += 1
    flags = {
        "cliff_1q":   any(g in CLIFFORD_1Q   for g in gates),
        "cliff_2q":   any(g in CLIFFORD_2Q   for g in gates),
        "t":          any(g in T_GATES       for g in gates),
        "rot_1q":     any(g in ROTATIONS_1Q  for g in gates),
        "rot_2q":     any(g in ROTATIONS_2Q  for g in gates),
        "threeplus":  any(g in THREE_PLUS    for g in gates),
        "unknown":    any(g not in (CLIFFORD_1Q | CLIFFORD_2Q | T_GATES |
                                    ROTATIONS_1Q | ROTATIONS_2Q | THREE_PLUS |
                                    OTHER)
                          for g in gates),
    }
    return {"gates": gates, "flags": flags, "n_qubits": qc.num_qubits,
            "n_clbits": qc.num_clbits, "size": sum(gates.values())}


def load_program(program_dir: str) -> tuple[str, QuantumCircuit] | None:
    """Locate the principal .qasm file in a QASMBench program directory."""
    if not os.path.isdir(program_dir):
        return None
    name = os.path.basename(program_dir)
    # Prefer {name}.qasm, fall back to {name}_transpiled.qasm.
    candidates = [os.path.join(program_dir, f"{name}.qasm"),
                  os.path.join(program_dir, f"{name}_transpiled.qasm")]
    for f in candidates:
        if os.path.isfile(f):
            try:
                qc = QuantumCircuit.from_qasm_file(f)
                return (name, qc)
            except Exception as e:
                print(f"  [parse error] {name}: {e}", file=sys.stderr)
                return None
    return None


def scan_bucket(bucket: str) -> list[dict]:
    """Scan all programs in one size bucket."""
    bucket_dir = os.path.join(QASMBENCH_ROOT, bucket)
    results = []
    for entry in sorted(os.listdir(bucket_dir)):
        program_dir = os.path.join(bucket_dir, entry)
        if not os.path.isdir(program_dir):
            continue
        loaded = load_program(program_dir)
        if loaded is None:
            continue
        name, qc = loaded
        info = classify_circuit(qc)
        info["name"] = name
        results.append(info)
    return results


def tag(flags: dict) -> str:
    parts = []
    if flags["cliff_1q"] or flags["cliff_2q"]: parts.append("C")
    if flags["t"]:         parts.append("T")
    if flags["rot_1q"] or flags["rot_2q"]: parts.append("R")
    if flags["threeplus"]: parts.append(">2")
    if flags["unknown"]:   parts.append("?")
    return "".join(parts)


def supported_today(flags: dict) -> bool:
    """True if the program uses only gates our compiler handles natively."""
    return (not flags["rot_1q"] and not flags["rot_2q"]
            and not flags["threeplus"] and not flags["unknown"])


def print_bucket(bucket: str, results: list[dict]) -> dict:
    print(f"\n=== {bucket.upper()} ({len(results)} programs) ===")
    print(f"  {'program':<30} {'n_q':>4} {'gates':>6}  classes  today?")
    print("  " + "-" * 70)
    n_supported = 0
    gate_union: Counter = Counter()
    for r in results:
        t = tag(r["flags"])
        supp = "YES" if supported_today(r["flags"]) else "no"
        if supported_today(r["flags"]):
            n_supported += 1
        gate_union.update(r["gates"])
        print(f"  {r['name']:<30} {r['n_qubits']:>4} {r['size']:>6}  {t:<7}  {supp}")
    print(f"  [supported today: {n_supported}/{len(results)}]")
    return {"bucket": bucket, "n_total": len(results), "n_supported": n_supported,
            "gate_union": gate_union}


def main():
    if not os.path.isdir(QASMBENCH_ROOT):
        print(f"QASMBench not found at {QASMBENCH_ROOT}")
        sys.exit(1)
    summary = []
    all_gates: Counter = Counter()
    for bucket in ["small", "medium", "large"]:
        res = scan_bucket(bucket)
        agg = print_bucket(bucket, res)
        summary.append(agg)
        all_gates.update(agg["gate_union"])

    print("\n" + "=" * 72)
    print("SUMMARY — native coverage of QMeas compiler (Cliff+T only):")
    print(f"  {'bucket':<10}  {'supported':>10}  {'total':>6}  {'%':>5}")
    for a in summary:
        pct = 100 * a["n_supported"] / a["n_total"] if a["n_total"] else 0
        print(f"  {a['bucket']:<10}  {a['n_supported']:>10}  {a['n_total']:>6}  {pct:>4.0f}%")

    print("\nDistinct gate names encountered across QASMBench:")
    for g, n in sorted(all_gates.items(), key=lambda x: -x[1])[:40]:
        cls = ("1q-Cliff" if g in CLIFFORD_1Q else
               "2q-Cliff" if g in CLIFFORD_2Q else
               "T" if g in T_GATES else
               "1q-rot"   if g in ROTATIONS_1Q else
               "2q-rot"   if g in ROTATIONS_2Q else
               "3+"       if g in THREE_PLUS else
               "other"    if g in OTHER else
               "unknown")
        print(f"  {g:<12}  {n:>8}  [{cls}]")


if __name__ == "__main__":
    main()
