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

-- Session: 17 October 2026. Characterize all fixed vectors.
theorem zz_fixed_iff (ψ : TwoQubitVector) :
    zzAction ψ = ψ ↔ ψ 1 = 0 ∧ ψ 2 = 0 := by
  constructor
  · intro h
    have h1 : -ψ 1 = ψ 1 := congrFun h 1
    have h2 : -ψ 2 = ψ 2 := congrFun h 2
    constructor
    · exact CharZero.neg_eq_self_iff.mp h1
    · exact CharZero.neg_eq_self_iff.mp h2
  · intro h
    ext i
    fin_cases i
    · rfl
    · change -ψ 1 = ψ 1
      rw [h.1]
      exact neg_zero
    · change -ψ 2 = ψ 2
      rw [h.2]
      exact neg_zero
    · rfl

-- Warm-up: extract and reverse coordinate conditions.
example (ψ : TwoQubitVector) (h : ψ 1 = 0 ∧ ψ 2 = 0) :
    ψ 2 = 0 := by
  exact h.2

example (ψ : TwoQubitVector) (h : ψ 1 = 0 ∧ ψ 2 = 0) :
    ψ 2 = 0 ∧ ψ 1 = 0 := by
  constructor
  · exact h.2
  · exact h.1

example (ψ : TwoQubitVector) (h1 : ψ 1 = 0) :
    zzAction ψ 1 = ψ 1 := by
  change -ψ 1 = ψ 1
  rw [h1]
  exact neg_zero

example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    -ψ 2 = ψ 2 := by
  have h2 := congrFun h 2
  exact h2

example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    ψ 2 = 0 := by
  have h2 : -ψ 2 = ψ 2 := congrFun h 2
  exact CharZero.neg_eq_self_iff.mp h2

example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    ψ 1 = 0 ∧ ψ 2 = 0 := by
  have h1 : -ψ 1 = ψ 1 := congrFun h 1
  have h2 : -ψ 2 = ψ 2 := congrFun h 2
  constructor
  · exact CharZero.neg_eq_self_iff.mp h1
  · exact CharZero.neg_eq_self_iff.mp h2

-- Use the forward and reverse directions of the named theorem.
example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    ψ 1 = 0 := by
  have m : ψ 1 = 0 := ((zz_fixed_iff ψ).mp h).1
  exact m

example (ψ : TwoQubitVector)
    (h1 : ψ 1 = 0) (h2 : ψ 2 = 0) :
    zzAction ψ = ψ := by
  have h : ψ 1 = 0 ∧ ψ 2 = 0 := by
    constructor
    · exact h1
    · exact h2
  have m : zzAction ψ = ψ := (zz_fixed_iff ψ).mpr h
  exact m

example (ψ : TwoQubitVector) (h : ψ 2 = 0 ∧ ψ 1 = 0) :
    zzAction ψ = ψ := by
  have k : ψ 1 = 0 ∧ ψ 2 = 0 := by
    constructor
    · exact h.2
    · exact h.1
  have m : zzAction ψ = ψ := ((zz_fixed_iff ψ).mpr) k
  exact m

-- Both vectors are fixed when their middle amplitudes vanish.
example (ψ φ : TwoQubitVector)
    (hψ : ψ 1 = 0 ∧ ψ 2 = 0)
    (hφ : φ 1 = 0 ∧ φ 2 = 0) :
    zzAction ψ = ψ ∧ zzAction φ = φ := by
  constructor
  have m : zzAction ψ = ψ := (zz_fixed_iff ψ).mpr hψ
  exact m
  have n : zzAction φ = φ := (zz_fixed_iff φ).mpr hφ
  exact n

-- A nonzero middle amplitude prevents a vector from being fixed.
example (ψ : TwoQubitVector) (hNonzero : ψ 1 ≠ 0) :
    zzAction ψ ≠ ψ := by
  intro hFixed
  have m : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hFixed).1
  exact hNonzero m

-- Either nonzero middle amplitude rules out a fixed vector.
example (ψ : TwoQubitVector)
    (h : ψ 1 ≠ 0 ∨ ψ 2 ≠ 0) :
    zzAction ψ ≠ ψ := by
  intro hFixed
  cases h with
  | inl F1 =>
      have m : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hFixed).1
      exact F1 m
  | inr F2 =>
      have n : ψ 2 = 0 := ((zz_fixed_iff ψ).mp hFixed).2
      exact F2 n


example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    -ψ 1 = ψ 1 := by
  have h1 := congrFun h 1
  exact h1

-- 1. Extract the other zero coordinate using zz_fixed_iff.
example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    ψ 2 = 0 := by
  have k: - (ψ 2) = ψ 2 := congrFun h 2
  exact CharZero.neg_eq_self_iff.mp k



-- 2. Package the characterization as an implication.
example (ψ : TwoQubitVector) :
    (ψ 1 = 0 ∧ ψ 2 = 0) → zzAction ψ = ψ := by
  intro h
  ext i
  fin_cases i
  · rfl
  · change -ψ 1 = ψ 1
    rw [h.1]
    exact neg_zero
  · change -ψ 2 = ψ 2
    rw [h.2]
    exact neg_zero
  · rfl



-- 3. Transfer the fixed-vector property across an equality.
example (ψ φ : TwoQubitVector)
    (hψ : zzAction ψ = ψ) (hEq : ψ = φ) :
    zzAction φ = φ :=by
    rw [← hEq]
    exact hψ


-- 4. If the second middle amplitude is nonzero, ψ cannot be fixed.
example (ψ : TwoQubitVector) (hNonzero : ψ 2 ≠ 0) :
    zzAction ψ ≠ ψ := by
  intro h
  have m : ψ 2 = 0 := ((zz_fixed_iff ψ).mp h).2
  exact hNonzero m

-- 5. Two fixed vectors have equal middle amplitudes.
example (ψ φ : TwoQubitVector)
    (hψ : zzAction ψ = ψ) (hφ : zzAction φ = φ) :
    ψ 1 = φ 1 ∧ ψ 2 = φ 2 := by
   have m1 : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hψ).1
   have n1 : φ 1 = 0 := ((zz_fixed_iff φ).mp hφ).1
   have m2 : ψ 2 = 0 := ((zz_fixed_iff ψ).mp hψ).2
   have n2 : φ 2 = 0 := ((zz_fixed_iff φ).mp hφ).2
   constructor
   rw [m1, n1]
   rw [m2, n2]


/- Part 1: Logic practice -/

-- 1. Assemble the zero-coordinate conditions.
example (ψ : TwoQubitVector)
    (h1 : ψ 1 = 0) (h2 : ψ 2 = 0) :
    ψ 1 = 0 ∧ ψ 2 = 0 := by
  constructor
  exact h1
  exact h2

-- 2. Extract a hypothesis from a nested conjunction.
example (ψ : TwoQubitVector)
    (h : ψ 0 = 0 ∧ (ψ 1 = 0 ∧ ψ 2 = 0)) :
    ψ 2 = 0 := by
  have hh: ψ 1 = 0 ∧ ψ 2 = 0 := h.2
  exact hh.2

-- 3. A fixed vector has its zero coordinates in either order.
example (ψ : TwoQubitVector) (h : zzAction ψ = ψ) :
    ψ 2 = 0 ∧ ψ 1 = 0 := by
    have m1 : ψ 1 = 0 := ((zz_fixed_iff ψ).mp h).1
    have m2 : ψ 2 = 0 := ((zz_fixed_iff ψ).mp h).2
    constructor
    exact m2
    exact m1



-- 4. If every coordinate vanishes, the vector is fixed.
example (ψ : TwoQubitVector)
    (h : ∀ i : Fin 4, ψ i = 0) :
    zzAction ψ = ψ := by
    ext i
    fin_cases i
    · rfl
    · change -ψ 1 = ψ 1
      rw [h 1]
      exact neg_zero
    · change -ψ 2 = ψ 2
      rw [h 2]
      exact neg_zero
    · rfl

-- 5. Either of these hypotheses suffices to prove ψ is fixed.
example (ψ : TwoQubitVector)
    (h : zzAction ψ = ψ ∨ (ψ 1 = 0 ∧ ψ 2 = 0)) :
    zzAction ψ = ψ := by
     cases h with
     | inl hE =>
        exact hE
     | inr hF =>
        ext i
        fin_cases i
        · rfl
        · change -ψ 1 = ψ 1
          rw [hF.1]
          exact neg_zero
        · change -ψ 2 = ψ 2
          rw [hF.2]
          exact neg_zero
        · rfl



/- Part 2: Coordinates and equalities -/

-- 6. Equal vectors have equal amplitudes at index 3.
example (ψ φ : TwoQubitVector) (h : ψ = φ) :
    ψ 3 = φ 3 := by
      have m1 : ψ 3 = φ 3 := congrFun h 3
      exact m1

-- 7. Transfer a zero amplitude across an equality of vectors.
example (ψ φ : TwoQubitVector)
    (hEq : ψ = φ) (h1 : ψ 1 = 0) :
    φ 1 = 0 := by
    have k: ψ (1) = φ (1) := congrFun hEq 1
    rw [← k]
    exact h1


-- 8. Applying ZZ preserves equality of vectors.
example (ψ φ : TwoQubitVector) (h : ψ = φ) :
    zzAction ψ = zzAction φ := by
  rw [h]

-- 9. Build vector equality from coordinate equalities.
example (ψ φ : TwoQubitVector)
    (h : ∀ i : Fin 4, ψ i = φ i) :
    ψ = φ := by
  ext i
  exact h i

-- 10. For fixed vectors, only the outer coordinates
--     are needed to establish equality.
example (ψ φ : TwoQubitVector)
    (hψ : zzAction ψ = ψ)
    (hφ : zzAction φ = φ)
    (h0 : ψ 0 = φ 0)
    (h3 : ψ 3 = φ 3) :
    ψ = φ := by
    have m1 : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hψ).1
    have m3 : ψ 2 = 0 := ((zz_fixed_iff ψ).mp hψ).2
    have m4 : φ 1 = 0 := ((zz_fixed_iff φ).mp hφ).1
    have m2 : φ 2 = 0 := ((zz_fixed_iff φ).mp hφ).2
    ext i
    fin_cases i
    · exact h0
    · calc
      ψ (1) = 0 := by
           exact m1
          _ = φ (1) := by
           symm
           exact m4
    · calc
      ψ (2) = 0 := by
           exact m3
          _ = φ (2) := by
           symm
           exact m2
    · exact h3


/- Part 3: Constructing fixed vectors -/

-- 11. The zero vector is fixed.
example :
    zzAction (fun _ => 0) = (fun _ => 0) := by
    apply (zz_fixed_iff _).mpr
    constructor
    · rfl
    ·  rfl




-- 12. A vector supported at index 0 is fixed.
example (a : ℂ) :
    zzAction (fun i => if i = 0 then a else 0) =
      (fun i => if i = 0 then a else 0) := by
       apply (zz_fixed_iff _).mpr
       constructor
       rfl
       rfl



-- 13. Negating a fixed vector produces a fixed vector.
example (ψ : TwoQubitVector) (hψ : zzAction ψ = ψ) :
    zzAction (fun i => -ψ i) = (fun i => -ψ i) := by
      apply (zz_fixed_iff _).mpr
      have m1 : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hψ).1
      have m2 : ψ 2 = 0 := ((zz_fixed_iff ψ).mp hψ).2
      constructor
      rw [m1]
      exact neg_zero
      rw [m2]
      exact neg_zero



-- 14. Adding two fixed vectors produces a fixed vector.
example (ψ φ : TwoQubitVector)
    (hψ : zzAction ψ = ψ)
    (hφ : zzAction φ = φ) :
    zzAction (fun i => ψ i + φ i) =
      (fun i => ψ i + φ i) := by
      apply (zz_fixed_iff _).mpr
      have m1 : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hψ).1
      have m2 : ψ 2 = 0 := ((zz_fixed_iff ψ).mp hψ).2
      have n1 : φ 1 = 0 := ((zz_fixed_iff φ).mp hφ).1
      have n2 : φ 2 = 0 := ((zz_fixed_iff φ).mp hφ).2
      constructor
      rw [m1, n1]
      simp
      rw [m2, n2]
      simp




-- 15. Multiplying every amplitude by a complex number
--     preserves the fixed-vector property.
example (c : ℂ) (ψ : TwoQubitVector)
    (hψ : zzAction ψ = ψ) :
    zzAction (fun i => c * ψ i) =
      (fun i => c * ψ i) := by
  apply (zz_fixed_iff _).mpr
  have m1 : ψ 1 = 0 := ((zz_fixed_iff ψ).mp hψ).1
  have m2 : ψ 2 = 0 := ((zz_fixed_iff ψ).mp hψ).2
  constructor
  simp
  right
  exact m1
  simp
  right
  exact m2





end ZZCodespace
