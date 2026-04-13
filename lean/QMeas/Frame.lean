/-
# Pauli frame algebra and propagation through Cliffords.

A Pauli frame on a single qubit is one of {I, X, Y, Z}.  We define:

  * `pauliMat`  : Pauli1 → Op 2     – the corresponding 2×2 unitary;
  * `mulPauli`  : Pauli1 → Pauli1 → Pauli1
                 – multiplication on the projective Pauli group (we drop
                   the global phase, which is unobservable);
  * `pushH`     : Pauli1 → Pauli1   – conjugate by H: H P H = pushH P;
  * `pushS`     : Pauli1 → Pauli1   – conjugate by S: S P S† = pushS P;

The `push*` functions are the entries of the Heisenberg-picture
Clifford-Pauli commutation table.  They are extended to whole Clifford
circuits by structural recursion in `pushCliff1`.

Composing the gadget compiler relies on these: when a previous gadget
emits a frame `P`, a subsequent Clifford `C` "sees" `pushCliff C P`
applied to its input instead of the bare Pauli, hence the QMeas program
must record `pushCliff C P` rather than `P` after `C`.
-/
import QMeas.Pauli
import QMeas.Syntax

namespace QMeas
namespace Frame

/-- Identify our `Pauli1` constructors with concrete 2×2 matrices.  We add
    a fourth `I` (identity) outside the `Pauli1` inductive (which only
    has X, Y, Z) by parameterizing on `Option Pauli1`: `none = I`. -/
noncomputable def pauliMat : Pauli1 → Op 2
  | .X => σX
  | .Y => σY
  | .Z => σZ

/-- Optional Pauli, with `none` = identity. -/
noncomputable def optPauliMat : Option Pauli1 → Op 2
  | none   => I2
  | some p => pauliMat p

/-- Pauli multiplication on the projective group (we drop global phase
    factors of `±1`, `±i`); we use `Option Pauli1` so identity has a
    canonical representative. -/
def mulOpt : Option Pauli1 → Option Pauli1 → Option Pauli1
  | none, q => q
  | p, none => p
  | some .X, some .X => none
  | some .Y, some .Y => none
  | some .Z, some .Z => none
  | some .X, some .Y => some .Z
  | some .Y, some .X => some .Z
  | some .Y, some .Z => some .X
  | some .Z, some .Y => some .X
  | some .Z, some .X => some .Y
  | some .X, some .Z => some .Y

/-! ### Clifford-Pauli commutation table (single-qubit gates).

For a Clifford `U` and Pauli `P`, `U · P = P' · U` where `P' = U P U†`.
The function `pushCliff U` returns `P'` given `P`.

  H X H = Z      H Z H = X      H Y H = -Y    (we ignore signs)
  S X S† = Y     S Y S† = -X    S Z S† = Z
-/

def pushH : Option Pauli1 → Option Pauli1
  | none => none
  | some .X => some .Z
  | some .Y => some .Y
  | some .Z => some .X

def pushS : Option Pauli1 → Option Pauli1
  | none => none
  | some .X => some .Y
  | some .Y => some .X
  | some .Z => some .Z

end Frame
end QMeas
