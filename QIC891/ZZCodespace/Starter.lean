import Mathlib.Data.Complex.Basic

/-
Project: the +1 eigenspace of Z tensor Z has complex dimension 2.
Start with Exercise 1 only. See README.md for the complete roadmap.

A vector is a function assigning a complex amplitude to each basis index:
  0 = |00>, 1 = |01>, 2 = |10>, 3 = |11>.
We include unnormalized vectors and the zero vector so that we can form
a complex vector subspace.
-/

namespace ZZCodespace

abbrev TwoQubitVector := Fin 4 → ℂ

-- Coordinate description of diag(1, -1, -1, 1).
-- A later milestone proves this agrees with the library's Z tensor Z.
def zzAction (ψ : TwoQubitVector) : TwoQubitVector :=
  fun i => if i = 0 ∨ i = 3 then ψ i else -ψ i

-- Exercise 1: ZZ leaves the |00> amplitude unchanged.
-- ψ 0 means the amplitude at index 0, not a normalized state.
-- First try the tactic used for equalities true by definition.
example (ψ : TwoQubitVector) : zzAction ψ 0 = ψ 0 := by
  sorry

-- Exercise 2: ZZ negates the |01> amplitude.
-- Attempt only after Exercise 1.
example (ψ : TwoQubitVector) : zzAction ψ 1 = -ψ 1 := by
  sorry

-- Exercise 3: ZZ negates the |10> amplitude.
example (ψ : TwoQubitVector) : zzAction ψ 2 = -ψ 2 := by
  sorry

-- Exercise 4: ZZ leaves the |11> amplitude unchanged.
example (ψ : TwoQubitVector) : zzAction ψ 3 = ψ 3 := by
  sorry

end ZZCodespace
