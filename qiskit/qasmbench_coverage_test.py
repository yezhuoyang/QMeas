"""QASMBench coverage test for the QMeas compiler front-end.

For every program in QASMBench (small / medium / large), we run
  QASM -> qiskit.transpile(basis={H, S, Sdg, T, Tdg, CX, X, Y, Z, Id, Rz})
       -> decompose all custom gates
       -> check: every surviving gate is in our supported set
and report PASS / FAIL per program.

A PASS means the program falls within the scope of our QMeas compiler:
every operation can be translated to a QMeas gadget (possibly with T
magic-state injection for Rz rotations after Solovay-Kitaev synthesis).

Unlike `qasmbench_benchmark.py` (which also runs the four optimization
pipelines), this script is a *coverage-only* check; it never runs the
compiler itself.  Fast enough to execute the whole suite in seconds.
"""

from __future__ import annotations
import os
import sys
import time
from collections import Counter

try:
    from qiskit import QuantumCircuit, transpile
except ImportError:
    print("qiskit not installed"); sys.exit(1)


QASMBENCH_ROOT = r"C:\Users\yezhu\Documents\MeasureLanguage\QASMBench"
# Our compiler's base set, plus the two gates the qiskit transpile path
# will pass through unchanged.
SUPPORTED_BASIS = {"h", "s", "sdg", "t", "tdg",
                   "cx", "cz", "swap",
                   "x", "y", "z", "id", "rz",
                   # QMeas natively supports classical control flow via its
                   # `IfPos` statement (see Section on Operational Semantics),
                   # so conditional gates from QASM `if(c==k) ...` map onto
                   # QMeas `if r=+1 then ...`.  We accept `if_else` as
                   # in-language.
                   "if_else",
                   "barrier", "measure", "reset", "delay"}


def check_coverage(qasm_path: str, decompose_depth: int = 8,
                   max_transpile_time_s: float = 30.0) -> dict:
    """Return a dict describing coverage status for one QASM file."""
    name = os.path.basename(qasm_path)
    t0 = time.time()
    try:
        qc = QuantumCircuit.from_qasm_file(qasm_path)
    except Exception as e:
        return {"name": name, "ok": False, "reason": f"parse: {str(e)[:80]}"}
    try:
        # Decompose custom gates (ccx, cswap, u3, etc.) down to primitives
        for _ in range(decompose_depth):
            qc = qc.decompose()
    except Exception as e:
        return {"name": name, "ok": False, "reason": f"decompose: {str(e)[:80]}"}
    try:
        qc = transpile(qc, basis_gates=list(SUPPORTED_BASIS - {"barrier",
                                                               "measure",
                                                               "reset",
                                                               "delay"}),
                       optimization_level=0)
    except Exception as e:
        return {"name": name, "ok": False, "reason": f"transpile: {str(e)[:80]}"}
    # Collect surviving gate names
    gates = Counter(inst.operation.name.lower() for inst in qc.data)
    elapsed = time.time() - t0
    if elapsed > max_transpile_time_s:
        return {"name": name, "ok": False, "reason": f"timeout ({elapsed:.1f}s)",
                "gates": gates, "n_qubits": qc.num_qubits, "elapsed_s": elapsed}
    unsupported = {g: c for g, c in gates.items() if g not in SUPPORTED_BASIS}
    if unsupported:
        return {"name": name, "ok": False,
                "reason": f"unsupported: {list(unsupported)[:3]}",
                "unsupported_gates": unsupported,
                "n_qubits": qc.num_qubits, "elapsed_s": elapsed}
    return {"name": name, "ok": True, "n_qubits": qc.num_qubits,
            "n_ops": sum(gates.values()), "gates": gates,
            "elapsed_s": elapsed}


def scan_bucket(bucket: str,
                skip_if_lines_gt: int | None = None) -> list[dict]:
    """Run coverage check for every program in a bucket."""
    bucket_dir = os.path.join(QASMBENCH_ROOT, bucket)
    results = []
    for entry in sorted(os.listdir(bucket_dir)):
        pd = os.path.join(bucket_dir, entry)
        if not os.path.isdir(pd):
            continue
        qasm = os.path.join(pd, f"{entry}.qasm")
        if not os.path.isfile(qasm):
            continue
        if skip_if_lines_gt is not None:
            with open(qasm) as f:
                n_lines = sum(1 for _ in f)
            if n_lines > skip_if_lines_gt:
                results.append({"name": entry, "ok": None,
                                "reason": f"skipped (>{skip_if_lines_gt} lines)",
                                "n_lines": n_lines})
                continue
        r = check_coverage(qasm)
        results.append(r)
    return results


def print_report(bucket: str, results: list[dict]):
    print(f"\n{'='*72}")
    print(f"QASMBench [{bucket.upper()}] — {len(results)} programs\n")
    print(f"  {'program':<30} {'n_qubits':>8}  {'status':<15}  note")
    print("  " + "-"*70)
    n_pass = 0; n_fail = 0; n_skip = 0
    for r in results:
        if r["ok"] is True:
            n_pass += 1
            mark = "PASS"
            note = f"{r['n_ops']} ops, {r['elapsed_s']:.1f}s"
        elif r["ok"] is False:
            n_fail += 1
            mark = "FAIL"
            note = r["reason"]
        else:
            n_skip += 1
            mark = "SKIP"
            note = r["reason"]
        nq = r.get("n_qubits", "?")
        print(f"  {r['name']:<30} {nq:>8}  {mark:<15}  {note}")
    tot = max(1, n_pass + n_fail)   # exclude skipped from denominator
    pct = 100.0 * n_pass / tot
    print(f"  ---  {n_pass}/{tot} PASS = {pct:.1f}% ({n_skip} skipped)")
    return {"bucket": bucket, "n_pass": n_pass, "n_fail": n_fail, "n_skip": n_skip}


def main():
    buckets = ["small"]
    if "--all" in sys.argv:
        buckets = ["small", "medium", "large"]

    agg = []
    for b in buckets:
        # Cap huge programs (>5 000 lines) to keep runtime bounded
        skip = None if b == "small" else 5000
        results = scan_bucket(b, skip_if_lines_gt=skip)
        agg.append(print_report(b, results))

    print(f"\n{'='*72}")
    print("COVERAGE SUMMARY")
    total_pass = 0; total_consider = 0
    for a in agg:
        den = a["n_pass"] + a["n_fail"]
        pct = 100.0 * a["n_pass"] / max(1, den)
        print(f"  {a['bucket']:<10}  {a['n_pass']:>3}/{den:<3}  ({pct:>5.1f}%)  "
              f"[{a['n_skip']} skipped]")
        total_pass += a["n_pass"]
        total_consider += den
    if total_consider:
        tot_pct = 100.0 * total_pass / total_consider
        print(f"  {'total':<10}  {total_pass:>3}/{total_consider:<3}  "
              f"({tot_pct:>5.1f}%)")


if __name__ == "__main__":
    main()
