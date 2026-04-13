/-
# Clifford → QMeas compiler.

We define `compile1 : Cliff1 → Stmt` for single-qubit Cliffords and
`compile2 : Cliff2 → Stmt` for two-qubit ones.  Each gate is translated to
its Pauli-measurement gadget.  Composition `seq c₁ c₂` translates to
`Stmt.seq` of the two compiled programs.

Qubit and bit naming.  A compiled circuit threads a "current logical
qubit" name through the gadgets: each gadget consumes the current logical
qubit and produces a fresh ancilla as the new logical qubit.  We use a
naming scheme indexed by a `Nat` counter that increases with every
compiled gate.

The compiler's correctness — that running `compile c` on input `|ψ⟩`
yields `denote c · |ψ⟩` modulo Pauli-frame corrections — is proved in
`QMeas.Soundness` (per-gate base cases proved; composition stated).
-/
import QMeas.Syntax
import QMeas.Clifford

namespace QMeas
namespace Compiler

/-! ### Gadget program templates

Each template is a closed `Stmt` parameterized by:
  * the input data qubit `q`,
  * the ancilla qubit `a`,
  * the bit names `r1, r2, …` for measurement outcomes.

The template emits the QMeas program from §QMeas examples in the paper. -/

/-- Hadamard gadget: ancilla `a` in `|0⟩`,
    `r1 := M_{ZX}(q,a); r2 := M_X(q);
     if r1 = -1 frame_Z(a); if r2 = -1 frame_X(a); discard q`. -/
def gadgetH (q a r1 r2 : Nat) : Stmt :=
  Stmt.chain
    [ .meas2 r1 .ZX q a
    , .meas1 r2 .X q
    , .ifPos r1 .skip (.frame .Z a)
    , .ifPos r2 .skip (.frame .X a)
    , .discard q ]

/-- Phase gadget: ancilla `a` in `|+⟩`,
    `r1 := M_{ZZ}(q,a); r2 := M_Y(q);` plus the per-branch Pauli-frame
    update derived in `Gadgets/S.lean`. -/
def gadgetS (q a r1 r2 : Nat) : Stmt :=
  Stmt.chain
    [ .meas2 r1 .ZZ q a
    , .meas1 r2 .Y q
    -- (+1, +1) → frame_Z(a)
    , .ifPos r1 (.ifPos r2 (.frame .Z a) .skip) .skip
    -- (-1, +1) → frame_Y(a)
    , .ifPos r1 .skip (.ifPos r2 (.frame .Y a) .skip)
    -- (-1, -1) → frame_X(a)
    , .ifPos r1 .skip (.ifPos r2 .skip (.frame .X a))
    , .discard q ]

/-- CNOT gadget (canonical lattice-surgery form, single ancilla `a` in `|+⟩`):
    `r1 := M_{ZZ}(c,a); r2 := M_{XX}(a,t); r3 := M_Z(a);
     if r2 = -1 frame_Z(c); if r1 ≠ r3 frame_X(t); discard a`. -/
def gadgetCNOT (c t a r1 r2 r3 : Nat) : Stmt :=
  Stmt.chain
    [ .meas2 r1 .ZZ c a
    , .meas2 r2 .XX a t
    , .meas1 r3 .Z a
    , .ifPos r2 .skip (.frame .Z c)
    -- if r1 ≠ r3 then frame_X(t)
    , .ifPos r1 (.ifPos r3 .skip (.frame .X t))
                (.ifPos r3 (.frame .X t) .skip)
    , .discard a ]

/-! ### Single-qubit compiler. -/

/-- Counts how many fresh names a single-qubit Clifford circuit will
    consume (one ancilla + two bits per `H` or `S` gate). -/
def freshCount1 : Cliff1 → Nat
  | .id        => 0
  | .H         => 3       -- ancilla a, bits r1, r2
  | .S         => 3
  | .seq c₁ c₂ => freshCount1 c₁ + freshCount1 c₂

/-- Compile a single-qubit Clifford circuit, threading a "current" qubit
    name `q` and a fresh-name counter `k` through gadget instantiations.
    Returns the compiled `Stmt` and the final logical-qubit name. -/
def compile1Aux : Cliff1 → (q : Nat) → (k : Nat) → Stmt × Nat
  | .id,        q, k => (.skip, q)
  | .H,         q, k => (gadgetH q k (k+1) (k+2), k)
  | .S,         q, k => (gadgetS q k (k+1) (k+2), k)
  | .seq c₁ c₂, q, k =>
      let (p₁, q') := compile1Aux c₁ q k
      let k' := k + freshCount1 c₁
      let (p₂, q'') := compile1Aux c₂ q' k'
      (.seq p₁ p₂, q'')

/-- Top-level single-qubit compiler: input qubit name `0`, fresh counter
    starts at `1`. -/
def compile1 (c : Cliff1) : Stmt :=
  (compile1Aux c 0 1).fst

/-! ### Two-qubit compiler.

Two-qubit Clifford circuits live on a fixed pair of qubits `(0, 1)`.  The
H/S gates use the single-qubit gadget on one of these.  CNOT introduces
its own fresh ancilla. -/

def freshCount2 : Cliff2 → Nat
  | .id        => 0
  | .H _       => 3
  | .S _       => 3
  | .CNOT      => 4         -- ancilla + 3 bits
  | .seq c₁ c₂ => freshCount2 c₁ + freshCount2 c₂

/-- Two-qubit compiler.  We track the current names of qubits 0 and 1 of
    the abstract two-qubit register; gadgets that "discard" a data qubit
    relabel that slot to the freshly-introduced ancilla. -/
def compile2Aux : Cliff2 → (q0 q1 : Nat) → (k : Nat) → Stmt × Nat × Nat
  | .id,         q0, q1, _ => (.skip, q0, q1)
  | .H ⟨0, _⟩,   q0, q1, k => (gadgetH q0 k (k+1) (k+2), k, q1)
  | .H ⟨1, _⟩,   q0, q1, k => (gadgetH q1 k (k+1) (k+2), q0, k)
  | .H ⟨n+2, h⟩, _,  _,  _ => absurd h (by omega)
  | .S ⟨0, _⟩,   q0, q1, k => (gadgetS q0 k (k+1) (k+2), k, q1)
  | .S ⟨1, _⟩,   q0, q1, k => (gadgetS q1 k (k+1) (k+2), q0, k)
  | .S ⟨n+2, h⟩, _,  _,  _ => absurd h (by omega)
  | .CNOT,       q0, q1, k =>
      -- ancilla = k, bits = k+1, k+2, k+3; q0 and q1 are unchanged.
      (gadgetCNOT q0 q1 k (k+1) (k+2) (k+3), q0, q1)
  | .seq c₁ c₂, q0, q1, k =>
      let (p₁, q0', q1') := compile2Aux c₁ q0 q1 k
      let k' := k + freshCount2 c₁
      let (p₂, q0'', q1'') := compile2Aux c₂ q0' q1' k'
      (.seq p₁ p₂, q0'', q1'')

def compile2 (c : Cliff2) : Stmt :=
  (compile2Aux c 0 1 2).fst

end Compiler
end QMeas
