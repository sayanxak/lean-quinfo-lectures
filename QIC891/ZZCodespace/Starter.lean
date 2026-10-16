import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

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
  rfl

-- Exercise 2: ZZ negates the |01> amplitude.
-- Attempt only after Exercise 1.
example (ψ : TwoQubitVector) : zzAction ψ 1 = -ψ 1 := by
  rfl

-- Exercise 3: ZZ negates the |10> amplitude.
example (ψ : TwoQubitVector) : zzAction ψ 2 = -ψ 2 := by
  rfl

-- Exercise 4: ZZ leaves the |11> amplitude unchanged.
example (ψ : TwoQubitVector) : zzAction ψ 3 = ψ 3 := by
  rfl


-- Exercise: applying ZZ twice restores the |01⟩ amplitude.
example (ψ : TwoQubitVector) :
    zzAction (zzAction ψ) 1 = ψ 1 := by
  change -(-ψ 1) = ψ 1
  rw [neg_neg]

-- Applying ZZ twice restores every coordinate.
example (ψ : TwoQubitVector) :
    zzAction (zzAction ψ) = ψ := by
  ext i
  fin_cases i
  · rfl
  · change -(-ψ 1) = ψ 1
    rw [neg_neg]
  · change -(-ψ 2) = ψ 2
    rw [neg_neg]
  · rfl

-- Extract coordinate equalities from an equality of vectors.
example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    -ψ 1 = ψ 1 := by
  have h1 := congrFun h 1
  exact h1

example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    -ψ 1 = ψ 1 ∧ -ψ 2 = ψ 2 := by
  constructor
  · have h1 := congrFun h 1
    exact h1
  · have h2 := congrFun h 2
    exact h2

example (z : ℂ) (h : -z = z) : z = 0 := by
  exact CharZero.neg_eq_self_iff.mp h

-- Fixed vectors have zero middle amplitudes.
example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    ψ 1 = 0 ∧ ψ 2 = 0 := by
  constructor
  · have h1 : -ψ 1 = ψ 1 := congrFun h 1
    exact CharZero.neg_eq_self_iff.mp h1
  · have h2 : -ψ 2 = ψ 2 := congrFun h 2
    exact CharZero.neg_eq_self_iff.mp h2

-- Conversely, zero middle amplitudes imply ZZ fixes the vector.
example (ψ : TwoQubitVector)
    (h1 : ψ 1 = 0) (h2 : ψ 2 = 0) :
    zzAction ψ = ψ := by
  ext i
  fin_cases i
  · rfl
  · change -ψ 1 = ψ 1
    rw [h1]
    exact neg_zero
  · change -ψ 2 = ψ 2
    rw [h2]
    exact neg_zero
  · rfl

end ZZCodespace
