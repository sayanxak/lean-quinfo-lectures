import QuantumInfo.States.Pure.Qubit
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-
Quantum gate practice, round 2. Solve one exercise at a time.
Here * composes gates; 1 is the identity gate.
Use exact, constructor, bullets, left/right, and library proofs.

H is the Hadamard gate.
S and T are phase gates: their matrices are diag(1, i) and
diag(1, exp(i*pi/4)), respectively.
The library handles the matrices; you only need the identities below.
-/

#check Qubit.H_sq
#check Qubit.S_sq
#check Qubit.T_sq

-- Exercise 4: two Hadamard gates undo each other.
example : Qubit.H * Qubit.H = 1 := by
  exact Qubit.H_sq


/-
Round 3: simplify longer gate sequences using one new tactic: rw.

`rw [some_equality]` replaces the left side of that equality by its
right side in the goal. It can also finish if the resulting sides match.

For example, `rw [Qubit.T_sq]` replaces T * T by S.
Unlike `exact`, rewriting can use an identity inside a larger expression.

Two useful general identities:
  one_mul U : 1 * U = U
  mul_one U : U * 1 = U
Use `rw [one_mul]` or `rw [mul_one]` to remove an identity gate.

Parentheses specify how products are grouped. They do not denote extra gates.
These are equalities of gates, so they hold for every input state.
-/

-- Exercise 9: cancel a pair of X gates next to a Z gate.
-- Hint: rewrite the X pair, then remove the identity gate.
example : (Qubit.X * Qubit.X) * Qubit.Z = Qubit.Z := by
    rw [Qubit.X_sq]
    rw [one_mul]

-- Exercise 10: two pairs of T gates give Z.
-- Hint: rw [Qubit.T_sq] rewrites both matching pairs.
-- Which library fact proves the resulting goal?
example : (Qubit.T * Qubit.T) * (Qubit.T * Qubit.T) = Qubit.Z := by
  rw [Qubit.T_sq]
  rw [Qubit.S_sq]


-- Exercise 11: four S gates give the identity.
-- Hint: replace each S pair. Identify the gate in the remaining goal.
example : (Qubit.S * Qubit.S) * (Qubit.S * Qubit.S) = 1 := by
  rw [Qubit.S_sq]
  rw [Qubit.Z_sq]
-- Exercise 12: cancel two H gates on the right of X.
-- Hint: the final identity is on the right, so choose the matching identity law.
example : Qubit.X * (Qubit.H * Qubit.H) = Qubit.X := by
  rw [Qubit.H_sq]
  rw [mul_one]

/-
Round 4: regrouping gates with associativity.

mul_assoc a b c proves (a * b) * c = a * (b * c).
This changes parentheses while preserving the order of the gates.
Gate multiplication is generally not commutative: do not swap gate order.

rw [mul_assoc]       moves from (a * b) * c to a * (b * c).
rw [← mul_assoc]     moves in the reverse direction.
Type \leftarrow followed by a space to enter ← in VS Code.

After regrouping, use the gate identities and identity laws you know.
-/

-- Exercise 13: regroup to put two H gates together, then cancel them.
-- Start with rw [mul_assoc]. Inspect the new goal before continuing.
example : (Qubit.X * Qubit.H) * Qubit.H = Qubit.X := by
  rw [mul_assoc]
  rw [Qubit.H_sq]
  rw [mul_one]


-- Exercise 14: regroup in the other direction to cancel an X pair.
-- Start with rw [← mul_assoc].
example : Qubit.X * (Qubit.X * Qubit.Z) = Qubit.Z := by
  rw [← mul_assoc]
  rw [Qubit.X_sq]
  rw [one_mul]

-- Exercise 15: regroup, then turn two T gates into S.
-- Choose the direction yourself. No identity gate is needed here.
example : (Qubit.H * Qubit.T) * Qubit.T = Qubit.H * Qubit.S := by
  rw [mul_assoc]
  rw [Qubit.T_sq]


example (U : 𝐔[Qubit]) (h : U * U = 1) :
    (U * U) * Qubit.X = Qubit.X := by
  rw [h]
  rw [one_mul]

example (U : 𝐔[Qubit]) (h : U * U = 1) :
    U * (U * Qubit.Z) = Qubit.Z := by
  rw [← mul_assoc]
  rw [h]
  rw [one_mul]

example (U V : 𝐔[Qubit]) (h : U * U = 1) :
    (V * U) * U = V := by
  rw [mul_assoc]
  rw [h]
  rw [mul_one]

  example (U V : 𝐔[Qubit])
    (hU : U * U = 1) (hV : V * V = 1) :
    (U * U) * (V * V) = 1 := by
   rw [hU]
   rw [hV]
   rw [mul_one]

example (U V : 𝐔[Qubit]) (h : U * U = 1) :
    ((U * U) * V = V) ∧ (V * (U * U) = V) := by
  constructor
  · rw [h]
    rw [one_mul]
  · rw [h]
    rw [mul_one]


example (U V : 𝐔[Qubit])
    (hU : U * U = 1) (hV : V * V = 1) :
    U * ((U * V) * V) = 1 := by
    rw [mul_assoc]
    rw [hV]
    rw [mul_one]
    rw [hU]

example (U V : 𝐔[Qubit]) (hV : V * V = 1) :
    (U * V) * V = U := by
    rw [mul_assoc]
    rw [hV]
    rw [mul_one]

example (U V : 𝐔[Qubit])
    (hUV : U * V = V * U)
    (hU : U * U = 1) :
    (U * V) * U = V := by
     rw [hUV]
     rw [mul_assoc]
     rw [hU]
     rw [mul_one]

example (U V : 𝐔[Qubit])
    (hUV : U * V = V * U)
    (hV : V * V = 1) :
    V * (U * V) = U := by
    rw [hUV]
    rw [← mul_assoc]
    rw [hV]
    rw [one_mul]

    example (U V : 𝐔[Qubit])
    (hUV : U * V = V * U)
    (hU : U * U = 1)
    (hV : V * V = 1) :
    (U * V) * (U * V) = 1 := by
     nth_rw 1 [hUV]

     rw [mul_assoc]
     rw [← mul_assoc U U V]
     rw [hU]
     rw [one_mul]
     rw [hV]

     example (U V : 𝐔[Qubit])
    (hUV : U * V = V * U) :
    (U * V) * U = U * (U * V) := by
      nth_rw 2 [hUV]
      rw [← mul_assoc U V U]

     example (p0 p1 : ℝ) (h : p0 + p1 = 1) :
       p1 + p0 = 1 := by
        rw [add_comm p1 p0]
        exact h


    example (p0 p1 : ℝ) (h : p0 + p1 = 1) :
    p1 = 1 - p0 := by
       linarith


    example (p0 p1 : ℝ)
    (hSum : p0 + p1 = 1)
    (h0 : 0 ≤ p0) :
    p1 ≤ 1 := by
      linarith

    example (p0 p1 : ℝ)
    (hSum : p0 + p1 = 1)
    (h0 : 0 ≤ p0)
    (h1 : 0 ≤ p1) :
    (p0 ≤ 1) ∧ (p1 ≤ 1) := by
     constructor
     linarith
     linarith


    example (p0 p1 : ℝ)
    (hSum : p0 + p1 = 1)
    (h0 : (3 : ℝ) / 4 ≤ p0) :
    p1 ≤ (1 : ℝ) / 4 := by
      linarith


    example (p0 p1 : ℝ)
    (hSum : p0 + p1 = 1) :
    (p0 ≤ p1) → (p0 ≤ (1 : ℝ) / 2) := by
     intro h
     linarith


example (p0 p1 : ℝ)
    (hSum : p0 + p1 = 1)
    (hOrder : p0 ≤ p1) :
    2 * p0 ≤ 1 := by
  have hHalf : p0 ≤ (1 : ℝ) / 2 := by
    linarith
  linarith only [hHalf]


example (p0 p1 p2 : ℝ)
    (hSum : p0 + p1 + p2 = 1)
    (h2 : (1 : ℝ) / 2 ≤ p2) :
    p0 + p1 ≤ (1 : ℝ) / 2 := by
    linarith

example (State : Type) (ψ : State)
    (U V : State → State)
    (hU : U ψ = ψ)
    (hV : V ψ = ψ) :
    U (V ψ) = ψ := by
    rw [hV]
    rw [hU]

example (State : Type) (ψ : State)
    (U V W : State → State)
    (hU : U ψ = ψ)
    (hV : V ψ = ψ)
    (hW : W ψ = ψ) :
    U (V (W ψ)) = ψ := by
     rw [hW]
     rw [hV]
     rw [hU]


example (State : Type) (ψ : State)
    (E R S : State → State)
    (hRecover : R (E ψ) = ψ)
    (hStable : S ψ = ψ) :
    S (R (E ψ)) = ψ := by
  rw [hRecover]
  rw [hStable]

 example (State : Type) (ψ : State)
    (E1 E2 R : State → State)
    (h1 : R (E1 ψ) = ψ)
    (h2 : R (E2 ψ) = ψ) :
    ∀ φ : State,
      (φ = E1 ψ ∨ φ = E2 ψ) → R φ = ψ := by
        intro φ hError
        cases hError with
       | inl hEq =>
      rw [hEq]
      exact h1
       | inr hEq =>
      rw [hEq]
      exact h2


  example (State : Type) (E R : State → State)
    (hRecover : ∀ ψ : State, R (E ψ) = ψ) :
    ∀ ψ : State, R (E ψ) = ψ := by
    intro ψ
    rw [hRecover ψ]

  example (State : Type) (E R S : State → State)
    (hRecover : ∀ ψ : State, R (E ψ) = ψ)
    (hStable : ∀ ψ : State, S ψ = ψ) :
    ∀ ψ : State, S (R (E ψ)) = ψ := by
     intro ψ
     rw [hRecover ψ]
     exact hStable ψ

example (State : Type) (E R S : State → State)
    (hRecover : ∀ ψ : State, R (E ψ) = ψ)
    (hStable : ∀ ψ : State, S ψ = ψ) :
    ∀ ψ : State, S (R (E ψ)) = ψ := by
      intro ψ
      rw [hRecover]
      exact hStable ψ

example (State : Type) (E1 E2 R : State → State)
    (h1 : ∀ ψ : State, R (E1 ψ) = ψ)
    (h2 : ∀ ψ : State, R (E2 ψ) = ψ) :
    ∀ ψ φ : State,
      (φ = E1 ψ ∨ φ = E2 ψ) → R φ = ψ := by
      intro ψ φ hError
      cases hError with
       | inl hEq =>
          rw [hEq]
          exact h1 ψ
       | inr hEq =>
          rw [hEq]
          exact h2 ψ

example (State : Type)
    (InCode : State → Prop)
    (E R : State → State)
    (hRecover : ∀ ψ : State, InCode ψ → R (E ψ) = ψ) :
    ∀ ψ : State, InCode ψ → R (E ψ) = ψ := by
  intro ψ hCode
  exact hRecover ψ hCode


example (State : Type)
    (InCode : State → Prop)
    (ψ : State)
    (hCode : InCode ψ) :
    InCode ψ := by
  exact hCode

  example (State : Type)
    (InCode : State → Prop)
    (hAll : ∀ ψ : State, InCode ψ)
    (ψ : State) :
    InCode ψ := by
   exact hAll ψ


   example (State : Type)
    (InCode Good : State → Prop)
    (ψ : State)
    (hRule : InCode ψ → Good ψ)
    (hCode : InCode ψ) :
    Good ψ := by
    exact hRule hCode

example (State : Type)
    (InCode Good : State → Prop)
    (hRule : ∀ ψ : State, InCode ψ → Good ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    Good ψ := by
    exact hRule ψ hCode

 example (State : Type)
    (InCode : State → Prop)
    (E R : State → State)
    (hRecover : ∀ ψ : State, InCode ψ → R (E ψ) = ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    R (E ψ) = ψ := by
    exact hRecover ψ hCode

example (State : Type)
    (InCode : State → Prop)
    (E R : State → State)
    (hRecover : ∀ ψ : State, InCode ψ → R (E ψ) = ψ) :
    ∀ ψ : State, InCode ψ → R (E ψ) = ψ := by
    intro ψ
    exact hRecover ψ



example (State : Type)
    (InCode : State → Prop)
    (S : State → State)
    (hStable : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    S ψ = ψ := by
    exact hStable ψ hCode

 example (State : Type)
    (InCode : State → Prop)
    (S T : State → State)
    (hS : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (hT : ∀ ψ : State, InCode ψ → T ψ = ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    S (T ψ) = ψ := by
    rw [hT ψ hCode]
    exact hS ψ hCode


  example (State : Type)
    (InCode : State → Prop)
    (S T : State → State)
    (hS : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (hT : ∀ ψ : State, InCode ψ → T ψ = ψ) :
    ∀ ψ : State, InCode ψ → S (T ψ) = ψ := by
    intro ψ
    intro hCode
    rw [hT ψ hCode]
    exact hS ψ hCode

   example : (1 : ZMod 2) + 1 = 0 := by
    decide

    example :
    ((1 : ZMod 2) + 1 = 0) ∧
    ((0 : ZMod 2) + 0 = 0) := by
     constructor
     decide
     decide

    example :
    ((1 : ZMod 2) + 0 = 1) ∧
    ((0 : ZMod 2) + 1 = 1) := by
      constructor
      decide
      decide

    def xBits : ZMod 2 × ZMod 2 := (1, 0)
    def zBits : ZMod 2 × ZMod 2 := (0, 1)
    example : xBits.1 = 1 := by
      rfl
      example : xBits.1 = 1 ∧ xBits.2 = 0 := by
       constructor
       rfl
       rfl
       def addBits (p q : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (p.1 + q.1, p.2 + q.2)
       example : addBits xBits zBits = (1, 1) := by
         unfold addBits xBits zBits
         rfl
       example : addBits xBits xBits = (0, 0) := by
          unfold addBits xBits
          decide
       example : addBits zBits zBits = (0, 0) := by
          decide
        def yBits : ZMod 2 × ZMod 2 := (1, 1)

        example : addBits yBits yBits = (0, 0) := by
           decide

def sympBit (p q : ZMod 2 × ZMod 2) : ZMod 2 :=
  p.1 * q.2 + p.2 * q.1
example : sympBit xBits zBits = 1 := by
        decide
example : sympBit xBits xBits = 0 := by
         decide
example : sympBit yBits xBits = 1 := by
         decide

example :
    sympBit xBits zBits + sympBit xBits zBits = 0 := by
       decide


def iBits : ZMod 2 × ZMod 2 := (0, 0)

example :
    sympBit xBits zBits +
    sympBit xBits zBits +
    sympBit iBits zBits = 0 := by
   decide

example :
    sympBit xBits zBits + sympBit iBits zBits = 1 := by
  decide

example :
    sympBit xBits zBits + sympBit xBits zBits = 0 := by
  decide

example :
    sympBit xBits zBits +
    sympBit xBits zBits +
    sympBit xBits zBits = 1 := by
  decide

example (p : ZMod 2 × ZMod 2) :
    addBits p iBits = p := by
    unfold addBits iBits
    simp

example (p : ZMod 2 × ZMod 2) :
    addBits iBits p = p := by
    simp [addBits, iBits]

example (p q : ZMod 2 × ZMod 2) :
    addBits p q = addBits q p := by
      unfold addBits
      congr 1
      exact add_comm p.1 q.1
      exact add_comm p.2 q.2

example (p q r : ZMod 2 × ZMod 2) :
    addBits (addBits p q) r = addBits p (addBits q r) := by
   unfold addBits
   congr 1
   simp
   exact add_assoc p.1 q.1 r.1
   simp
   exact add_assoc p.2 q.2 r.2

example (p : ZMod 2 × ZMod 2) :
    addBits p iBits = p ∧ addBits iBits p = p := by
  constructor
  simp [addBits, iBits]
  simp [addBits, iBits]

example (p q : ZMod 2 × ZMod 2)
    (h : addBits p q = iBits) :
    addBits q p = iBits := by
  simp [addBits, add_comm] at h ⊢
  exact h

  example (State : Type) (ψ : State)
    (E R S : State → State)
    (hRecover : R (E ψ) = ψ)
    (hStable : S ψ = ψ) :
    S (R (E ψ)) = ψ := by
    rw [hRecover]
    rw [hStable]

example (State : Type) (S : State → State)
    (hStable : ∀ ψ : State, S ψ = ψ) :
    ∀ ψ : State, S (S ψ) = ψ := by
     intro ψ
     rw [hStable ψ]
     exact hStable ψ

example (State : Type)
    (InCode : State → Prop)
    (S : State → State)
    (hStable : ∀ ψ : State, InCode ψ → S ψ = ψ) :
    ∀ ψ : State, InCode ψ → S (S ψ) = ψ := by
    intro ψ
    intro hCode
    rw [hStable ψ hCode]
    exact hStable ψ hCode

example (State : Type)
    (InCode : State → Prop)
    (S T : State → State)
    (hS : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (hT : ∀ ψ : State, InCode ψ → T ψ = ψ) :
    ∀ ψ : State, InCode ψ →
      (S ψ = ψ ∧ T ψ = ψ) := by
   intro ψ
   intro hCode
   constructor
   exact hS ψ hCode
   exact hT ψ hCode

example (State : Type) (ψ : State)
    (S T : State → State)
    (h : S ψ = ψ ∧ T ψ = ψ) :
    S (T ψ) = ψ := by
    rw [h.2]
    exact h.1

example (P Q : ℕ → Prop)
    (hP : ∃ a : ℕ, P a)
    (hQ : ∃ b : ℕ, Q b) :
    ∃ a b : ℕ, Q b ∧ P a := by
    obtain ⟨a, ha⟩ := hP
    obtain ⟨ b, hb⟩ := hQ
    use a
    use b

example (P : ℕ → Prop)
    (h : ∃ a : ℕ, ∃ b : ℕ, P (a + b)) :
    ∃ n : ℕ, P n := by
  obtain ⟨a , ha ⟩ := h
  obtain ⟨ b, hab⟩ := ha
  let n := a+b
  use n

example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n)
    (hRule : ∀ n : ℕ, P n → Q (n + 1)) :
    ∃ m : ℕ, Q m := by
  obtain ⟨ n, hn⟩ := h
  let qn := hRule n hn
  let m := n+1
  use m

example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n)
    (hRule : ∀ n : ℕ, P n → ∃ m : ℕ, Q m) :
    ∃ m : ℕ, Q m := by
  obtain ⟨ n, hn ⟩ := h
  let hhn := hRule n hn
  obtain ⟨ m, hhm⟩ := hhn
  use m

example (State : Type) (ψ : State)
    (R : State → State)
    (h : ∃ E : State → State, R (E ψ) = ψ) :
    ∃ φ : State, R φ = ψ := by
  obtain ⟨ E, RE⟩ := h
  let φ := E ψ
  use φ
