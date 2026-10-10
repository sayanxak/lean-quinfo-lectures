import QuantumInfo.States.Pure.Qubit

/-
Very easy quantum gate practice. Attempt one exercise at a time.

Qubit.X is the Pauli X gate (a bit flip).
Qubit.Z is the Pauli Z gate (a phase flip).
Here * composes gates, and 1 is the identity gate.

The library already proves the gate identities. Our first task is to
reuse its proofs, rather than calculate their matrices ourselves.
-/

-- Exercise 1: two bit flips undo each other.
-- Inspect the library fact, then supply it using `exact`.
#check Qubit.X_sq

example : Qubit.X * Qubit.X = 1 := by
  exact Qubit.X_sq

-- Exercise 2: two phase flips undo each other.
-- Try this only after Exercise 1.
#check Qubit.Z_sq

example : Qubit.Z * Qubit.Z = 1 := by
  exact Qubit.Z_sq

-- Exercise 3: prove both facts together using `constructor` and bullets.
example : (Qubit.X * Qubit.X = 1) ∧ (Qubit.Z * Qubit.Z = 1) := by
  constructor
  exact Qubit.X_sq
  exact Qubit.Z_sq
