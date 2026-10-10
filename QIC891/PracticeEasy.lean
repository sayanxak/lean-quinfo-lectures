import Mathlib.Data.Nat.Basic

/-
Practice: counting two groups of measurement outcomes.

zeros and ones are natural numbers (0, 1, 2, ...).
Prove that adding the two counts in either order gives the same total.

Inspect the library fact below. It takes two numbers as inputs.
Use `exact` with that fact and the two counts to replace `sorry`.
-/

#check Nat.add_comm

example (zeros ones : ℕ) : zeros + ones = ones + zeros := by
  exact Nat.add_comm zeros ones
