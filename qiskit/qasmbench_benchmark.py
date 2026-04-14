"""Run the full QMeas compiler + optimization pipeline on every program in
QASMBench and report coverage + optimization savings.

For each program:
  1. Parse QASM, transpile to {H, S, Sdg, T, Tdg, CX, Paulis, Rz}.
  2. Compile to QMeas.
  3. Run the four pipelines:
       naive / gate-first / meas-first / combined.
  4. Record measurement count, depth, pipeline winner, and time.

A program is "covered" if its transpile yields only known gate names;
otherwise the unresolved gate names are recorded.
"""

from __future__ import annotations
import os
import sys
import time
from collections import Counter

from compare_optimizers import meas_count, meas_depth, meas_optimize
from qmeas_extended import (compile_extended, gate_optimize_extended,
                             qasm_to_gate_list)

QASMBENCH_ROOT = r"C:\Users\yezhu\Documents\MeasureLanguage\QASMBench"
PER_PROGRAM_TIMEOUT_S = 60.0


def four_pipelines(gates: list[tuple]) -> dict:
    """Run all four pipelines and return (count, depth) for each."""
    results = {}
    # naive
    p = compile_extended(gates)
    results["naive"] = (meas_count(p), meas_depth(p))
    # gate-first
    p = compile_extended(gate_optimize_extended(gates))
    results["gate_first"] = (meas_count(p), meas_depth(p))
    # meas-first
    p = meas_optimize(compile_extended(gates))
    results["meas_first"] = (meas_count(p), meas_depth(p))
    # combined
    p = meas_optimize(compile_extended(gate_optimize_extended(gates)))
    results["combined"] = (meas_count(p), meas_depth(p))
    return results


def run_program(program_dir: str) -> dict | None:
    name = os.path.basename(program_dir)
    # Prefer the non-transpiled file so we exercise our own transpile path.
    qasm = os.path.join(program_dir, f"{name}.qasm")
    if not os.path.isfile(qasm):
        return None
    t0 = time.time()
    try:
        gates, unresolved = qasm_to_gate_list(qasm)
    except Exception as e:
        return {"name": name, "status": "parse_error", "error": str(e)[:120]}
    if unresolved:
        return {"name": name, "status": "unsupported_gates",
                "unresolved": sorted(unresolved),
                "n_gates": len(gates)}
    if time.time() - t0 > PER_PROGRAM_TIMEOUT_S:
        return {"name": name, "status": "transpile_timeout"}
    try:
        pipelines = four_pipelines(gates)
    except Exception as e:
        return {"name": name, "status": "compile_error", "error": str(e)[:120]}
    elapsed = time.time() - t0
    return {"name": name, "status": "ok", "n_gates": len(gates),
            "pipelines": pipelines, "time_s": elapsed}


def run_bucket(bucket: str, size_limit: int | None = None) -> list[dict]:
    """Run every program in one QASMBench bucket; size_limit skips
    programs larger than that many gates (to keep runtime bounded)."""
    bucket_dir = os.path.join(QASMBENCH_ROOT, bucket)
    results = []
    for entry in sorted(os.listdir(bucket_dir)):
        pd = os.path.join(bucket_dir, entry)
        if not os.path.isdir(pd):
            continue
        # Quick size check
        qasm = os.path.join(pd, f"{entry}.qasm")
        if os.path.isfile(qasm) and size_limit:
            with open(qasm) as f:
                n_lines = sum(1 for _ in f)
            if n_lines > size_limit:
                results.append({"name": entry, "status": "skipped_large",
                                 "n_lines": n_lines})
                continue
        res = run_program(pd)
        if res is not None:
            results.append(res)
    return results


def print_bucket_report(bucket: str, results: list[dict]):
    __import__("sys").stdout.flush(); print(f"\n{'='*100}")
    __import__("sys").stdout.flush(); print(f"QASMBench [{bucket.upper()}] — {len(results)} programs\n")
    __import__("sys").stdout.flush(); print(f"{'program':<28} {'gates':>6}  {'naive':>9}  {'gate-1st':>9}  "
          f"{'meas-1st':>9}  {'combined':>9}  {'status':<20}")
    __import__("sys").stdout.flush(); print("-" * 100)
    n_ok = 0; n_skipped = 0; n_unsup = 0
    strict_combined_wins = 0
    tot = {"naive":[0,0], "gate_first":[0,0], "meas_first":[0,0], "combined":[0,0]}
    for r in results:
        if r["status"] == "ok":
            n_ok += 1
            p = r["pipelines"]
            for k in tot:
                tot[k][0] += p[k][0]
                tot[k][1] += p[k][1]
            # strict combined-wins-both
            cc = p["combined"][0]
            if cc < p["gate_first"][0] and cc < p["meas_first"][0]:
                strict_combined_wins += 1
            __import__("sys").stdout.flush(); print(f"{r['name']:<28} {r['n_gates']:>6}  "
                  f"{p['naive'][0]:>4}/{p['naive'][1]:<3} "
                  f" {p['gate_first'][0]:>4}/{p['gate_first'][1]:<3} "
                  f" {p['meas_first'][0]:>4}/{p['meas_first'][1]:<3} "
                  f" {p['combined'][0]:>4}/{p['combined'][1]:<3}  "
                  f"ok ({r['time_s']:.1f}s)")
        elif r["status"] == "skipped_large":
            n_skipped += 1
            __import__("sys").stdout.flush(); print(f"{r['name']:<28} {r.get('n_lines','?'):>6}  "
                  f"{'':>9}  {'':>9}  {'':>9}  {'':>9}  "
                  f"skipped (large)")
        elif r["status"] == "unsupported_gates":
            n_unsup += 1
            u = ",".join(r["unresolved"])[:30]
            __import__("sys").stdout.flush(); print(f"{r['name']:<28} {r['n_gates']:>6}  "
                  f"{'':>9}  {'':>9}  {'':>9}  {'':>9}  "
                  f"unresolved: {u}")
        else:
            __import__("sys").stdout.flush(); print(f"{r['name']:<28} {'':>6}  {'':>9}  {'':>9}  {'':>9}  {'':>9}  "
                  f"{r['status']}")
    __import__("sys").stdout.flush(); print()
    __import__("sys").stdout.flush(); print(f"Summary: {n_ok} ok, {n_unsup} unresolved-gate, {n_skipped} skipped-large")
    if n_ok:
        __import__("sys").stdout.flush(); print(f"  avg count : naive={tot['naive'][0]/n_ok:.1f}  "
              f"gate={tot['gate_first'][0]/n_ok:.1f}  "
              f"meas={tot['meas_first'][0]/n_ok:.1f}  "
              f"combined={tot['combined'][0]/n_ok:.1f}")
        __import__("sys").stdout.flush(); print(f"  avg depth : naive={tot['naive'][1]/n_ok:.1f}  "
              f"gate={tot['gate_first'][1]/n_ok:.1f}  "
              f"meas={tot['meas_first'][1]/n_ok:.1f}  "
              f"combined={tot['combined'][1]/n_ok:.1f}")
        __import__("sys").stdout.flush(); print(f"  combined strictly beats both one-sided pipelines on "
              f"{strict_combined_wins}/{n_ok} programs")
    return {"bucket": bucket, "n_ok": n_ok, "n_unsup": n_unsup,
             "n_skipped": n_skipped, "strict_wins": strict_combined_wins,
             "totals": tot}


def main():
    # Only small for the first pass — medium/large have programs with
    # hundreds of thousands of gates.
    buckets = ["small"]
    if "--all" in sys.argv:
        buckets = ["small", "medium", "large"]

    aggregate = []
    for bucket in buckets:
        size_limit = None if bucket == "small" else 5_000   # lines
        results = run_bucket(bucket, size_limit=size_limit)
        agg = print_bucket_report(bucket, results)
        aggregate.append(agg)

    __import__("sys").stdout.flush(); print("\n" + "=" * 100)
    __import__("sys").stdout.flush(); print("OVERALL QASMBENCH COVERAGE + OPTIMIZATION REPORT")
    for agg in aggregate:
        __import__("sys").stdout.flush(); print(f"  {agg['bucket']:<10} ok={agg['n_ok']:>3}  "
              f"unresolved={agg['n_unsup']:>3}  "
              f"skipped={agg['n_skipped']:>3}  "
              f"combined strictly wins on {agg['strict_wins']}")


if __name__ == "__main__":
    main()
