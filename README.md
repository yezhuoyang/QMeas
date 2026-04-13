# QMeas — A verified Pauli-measurement language

This repository is the code artifact for the POPL submission *"A verified
compiler and optimizer for Pauli Measurement based quantum programs"* (Ye &
Palsberg, UCLA).  It contains:

- a **Lean 4** formalization (mathlib4) of three core measurement-based
  gadgets — Hadamard `H`, phase gate `S`, and `CNOT` — proved correct in
  every measurement branch with no `sorry`s;
- a **Qiskit** cross-check harness that mirrors each Lean theorem statement
  and verifies the algebraic identity numerically on random complex inputs.

```
.
├── lean/
│   ├── lakefile.toml        # mathlib v4.29.0
│   ├── lean-toolchain
│   └── QMeas/
│       ├── Pauli.lean       # I, X, Y, Z, H, S, kron2 …  (4×4)
│       ├── QState.lean      # Vec n, applyOp, projector, postMeas
│       ├── Syntax.lean      # QMeas program syntax
│       ├── Semantics.lean   # configuration, frame, store
│       └── Gadgets/
│           ├── H.lean       # H_gadget_correct
│           ├── S.lean       # S_gadget_correct
│           └── CNOT.lean    # CNOT_gadget_correct (8 branches)
├── qiskit/
│   ├── validate_gadgets.py        # exhaustive simulation of any 2-meas gadget
│   ├── search_gadgets.py          # search over Pauli measurement triples
│   ├── verify_chosen_gadgets.py   # 50-seed verification of the chosen gadgets
│   ├── derive_cnot_branches.py    # symbolic per-branch states for CNOT
│   └── cross_check_lean.py        # mirror the Lean state defs and re-verify
└── paper/                          # paper artifact (TBD)
```

## The verified gadgets

All three gadgets store every byproduct as a classical Pauli frame; the
gadgets themselves contain only Pauli measurements (no physical Cliffords).

### Hadamard
```
ancilla a in |0>
r1 := M_{ZX}(q, a)
r2 := M_X(q)
if r1 == -1 : frame_Z(a)
if r2 == -1 : frame_X(a)
discard q
```

### Phase gate S
```
ancilla a in |+>
r1 := M_{ZZ}(q, a)
r2 := M_Y(q)
if r1 == +1 ∧ r2 == +1 : frame_Z(a)
if r1 == -1 ∧ r2 == +1 : frame_Y(a)
if r1 == -1 ∧ r2 == -1 : frame_X(a)
discard q
```

### CNOT (canonical lattice-surgery)
```
ancilla a in |+>
r1 := M_{ZZ}(c, a)
r2 := M_{XX}(a, t)
r3 := M_Z(a)
if r2 == -1 : frame_Z(c)
if r1 ≠ r3  : frame_X(t)
discard a
```

## Build & verify

### Lean
```bash
cd lean
lake exe cache get        # download mathlib oleans
lake build                # builds all of QMeas, including the three gadget proofs
```

### Qiskit
```bash
cd qiskit
python validate_gadgets.py        # sanity check on the original (pre-fix) paper gadgets
python verify_chosen_gadgets.py   # 50-seed correctness of the corrected gadgets
python cross_check_lean.py        # ensure Lean theorem statements match physics
```

The cross-check script is the reproducible safety net: if any Lean state
definition were inconsistent with what a real measurement produces, this
script would detect it.

## Status

| Component                                      | Status        |
|-----------------------------------------------|---------------|
| H gadget — Lean proof, all 4 branches         | ✅ no sorry   |
| S gadget — Lean proof, all 4 branches         | ✅ no sorry   |
| CNOT gadget — Lean proof, all 8 branches      | ✅ no sorry   |
| Qiskit cross-check                             | ✅ all pass   |
| Operational small-step semantics (formalized) | sketched      |
| Soundness of the Clifford → QMeas compiler    | sketched      |
| Optimizer rules                                | future work   |
