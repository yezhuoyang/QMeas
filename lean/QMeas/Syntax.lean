/-
# QMeas syntax.

A QMeas program is a sequence of basic commands: single- and two-qubit Pauli
measurements (storing outcomes in classical bits), Pauli-frame updates
(`frameX/Y/Z`), conditionals on classical bits, bounded for-loops, and a
no-op `skip`.

We index quantum registers by `Nat`.  A QMeas program is a syntactic object,
independent of the operational semantics in `QMeas.Semantics`.
-/

namespace QMeas

/-- Single-qubit Pauli labels for measurement bases and frame updates. -/
inductive Pauli1 | X | Y | Z
  deriving DecidableEq, Repr

/-- Two-qubit Pauli labels for joint measurements. -/
inductive Pauli2 | XX | ZZ | XZ | ZX | YZ | ZY | YX | XY | YY
  deriving DecidableEq, Repr

/-- A QMeas command.  `Reg` is the type of quantum register names,
    `Bit`  is the type of classical bit names. -/
inductive Stmt where
  /-- No-op. -/
  | skip : Stmt
  /-- `r := M_P(q)` for single-qubit Pauli `P`. -/
  | meas1 (r : Nat) (P : Pauli1) (q : Nat) : Stmt
  /-- `r := M_P(qa, qb)` for two-qubit Pauli `P`. -/
  | meas2 (r : Nat) (P : Pauli2) (qa qb : Nat) : Stmt
  /-- Pauli-frame update on a single qubit. -/
  | frame (P : Pauli1) (q : Nat) : Stmt
  /-- Sequencing. -/
  | seq : Stmt → Stmt → Stmt
  /-- `if r = +1 then s1 else s2` (treats classical-bit value as ±1). -/
  | ifPos (r : Nat) (s1 s2 : Stmt) : Stmt
  /-- Bounded for-loop: iterate `body` exactly `N` times.  The iteration
      index is not exposed to the body (the body runs the same program
      each time, modulo its reads of the classical store).  A
      reader-visible counter would be a straightforward extension;
      it is omitted here because the original `i` parameter was a
      ghost (reviewer R07 in `reviewer_plan.md`). -/
  | forLoop (N : Nat) (body : Stmt) : Stmt
  /-- Discard a quantum register from the live set. -/
  | discard (q : Nat) : Stmt
  /-- `abort` — stuck terminal used for post-selection (e.g.\ in cultivation).
      No reduction rule fires on `abort`; multi-step reductions starting from
      the initial configuration partition into "accepted" (end in `skip`) and
      "rejected" (end in `abort`).  See `theory.tex` §Post-selection via abort. -/
  | abort : Stmt
  deriving Repr

/-- A QMeas program is just a top-level statement. -/
abbrev Prog := Stmt

/-- Convenience: chain a list of statements with `seq`. -/
def Stmt.chain : List Stmt → Stmt
  | []      => .skip
  | [s]     => s
  | s :: ss => .seq s (Stmt.chain ss)

end QMeas
