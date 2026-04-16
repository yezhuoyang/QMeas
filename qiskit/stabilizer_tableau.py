"""
Aaronson-Gottesman stabilizer tableau for the QMeas optimizer (R19).

Tracks the stabilizer group of an n-qubit state as measurements are
applied.  Used by `_r7_stabilizer_derivation` in `compare_optimizers.py`
to detect deterministic measurements (those whose observable is already
in the stabilizer group or its negation).

Reference: Aaronson & Gottesman, quant-ph/0406196.
"""

from __future__ import annotations

_PAULI_INDEX = {"I": 0, "X": 1, "Y": 2, "Z": 3}
_PAULI_NAME  = ["I", "X", "Y", "Z"]

# Pauli multiplication table  (a * b -> (phase_exp, result))
# phase_exp is the power of i in the product: P_a P_b = i^phase_exp P_result
_MUL_PHASE = [
    [0, 0, 0, 0],  # I * {I,X,Y,Z}
    [0, 0, 1, 3],  # X * {I,X,Y,Z}  -> {I,I,Z,-Z} => phases {0,0,+i,-i}
    [0, 3, 0, 1],  # Y * ...
    [0, 1, 3, 0],  # Z * ...
]
_MUL_RESULT = [
    [0, 1, 2, 3],
    [1, 0, 3, 2],
    [2, 3, 0, 1],
    [3, 2, 1, 0],
]


class PauliString:
    """A Pauli string on named qubits with a ±1 sign."""

    __slots__ = ("ops", "sign")

    def __init__(self, qubit_paulis: dict[str, int] | None = None, sign: int = 1):
        self.ops: dict[str, int] = dict(qubit_paulis) if qubit_paulis else {}
        self.sign = sign

    def copy(self) -> PauliString:
        return PauliString(self.ops, self.sign)

    def commutes_with(self, other: PauliString) -> bool:
        phase = 0
        for q in self.ops:
            if q in other.ops:
                a, b = self.ops[q], other.ops[q]
                if a != 0 and b != 0 and a != b:
                    phase += 1
        return phase % 2 == 0

    def multiply_by(self, other: PauliString) -> None:
        total_phase = 0
        for q, b in other.ops.items():
            a = self.ops.get(q, 0)
            total_phase += _MUL_PHASE[a][b]
            result = _MUL_RESULT[a][b]
            if result == 0:
                self.ops.pop(q, None)
            else:
                self.ops[q] = result
        # sign update: i^total_phase contributes ±1 only when total_phase is even
        # i^0 = 1, i^1 = i, i^2 = -1, i^3 = -i
        real_sign = [1, 1, -1, -1][total_phase % 4]
        self.sign *= other.sign * real_sign

    def remove_qubit(self, q: str) -> None:
        self.ops.pop(q, None)


class StabilizerTableau:
    """Stabilizer-group tracker for a set of named qubits.

    Starts empty (no qubits).  Qubits and stabilizers are added as
    measurements are processed.
    """

    def __init__(self):
        self.generators: list[PauliString] = []

    def is_determined(self, pauli_str: str, qubits: list[str]) -> tuple[bool, int]:
        """Check whether a Pauli measurement is deterministic.

        Returns (True, outcome) if the observable is (up to sign) in the
        stabilizer group, (False, 0) otherwise.

        The observable is the tensor product of single-qubit Paulis
        `pauli_str[i]` on `qubits[i]`.
        """
        obs = PauliString(
            {q: _PAULI_INDEX[p] for q, p in zip(qubits, pauli_str) if p != "I"},
            sign=1,
        )

        # Find an anticommuting generator.
        ac_idx = None
        for i, g in enumerate(self.generators):
            if not g.commutes_with(obs):
                ac_idx = i
                break

        if ac_idx is not None:
            return False, 0

        # The observable commutes with all generators.  Check if the
        # observable is a product of generators (i.e., in the stabilizer
        # group).  We do a simple Gaussian-elimination-style check by
        # trying to reduce obs to identity via multiplying by generators.
        probe = obs.copy()
        for g in self.generators:
            # If probe shares a non-identity entry with g on any qubit,
            # multiply to try to cancel.
            shared = False
            for q in list(probe.ops):
                if q in g.ops and probe.ops[q] != 0 and g.ops[q] != 0:
                    shared = True
                    break
            if shared:
                probe.multiply_by(g)

        if not probe.ops:
            return True, probe.sign
        return False, 0

    def measure(self, pauli_str: str, qubits: list[str]) -> None:
        """Record a non-deterministic measurement: update the stabilizer
        group by replacing the first anticommuting generator with the
        measured observable (Aaronson-Gottesman update rule)."""
        obs = PauliString(
            {q: _PAULI_INDEX[p] for q, p in zip(qubits, pauli_str) if p != "I"},
            sign=1,
        )

        ac_idx = None
        for i, g in enumerate(self.generators):
            if not g.commutes_with(obs):
                ac_idx = i
                break

        if ac_idx is None:
            # Observable already commutes with everything; just add it
            # if it's independent.
            self.generators.append(obs)
            return

        # Propagate: multiply all OTHER anticommuting generators by
        # generators[ac_idx] so they commute with obs.
        for i in range(len(self.generators)):
            if i != ac_idx and not self.generators[i].commutes_with(obs):
                self.generators[i].multiply_by(self.generators[ac_idx])

        # Replace the anticommuting generator with the observable.
        self.generators[ac_idx] = obs

    def discard(self, qubit: str) -> None:
        """Remove a qubit from all stabilizer generators."""
        new_gens = []
        for g in self.generators:
            g.remove_qubit(qubit)
            if g.ops:
                new_gens.append(g)
        self.generators = new_gens
