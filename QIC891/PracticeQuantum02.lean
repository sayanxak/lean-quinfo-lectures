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

example (State : Type) (ψ : State)
    (S T : State → State)
    (h : S ψ = ψ ∧ T ψ = ψ) :
    S (T (S ψ)) = ψ := by
  rw [h.1]
  rw [h.2]
  exact h.1

example (State : Type)
    (InCode : State → Prop)
    (S T : State → State)
    (h : ∀ ψ : State, InCode ψ →
      (S ψ = ψ ∧ T ψ = ψ)) :
    ∀ ψ : State, InCode ψ → S (T ψ) = ψ := by
  intro ψ
  intro F
  have hBoth := h ψ F
  rw [hBoth.2]
  rw [hBoth.1]

example (State : Type)
    (InCode : State → Prop)
    (E R S : State → State)
    (hRecover : ∀ ψ : State, InCode ψ → R (E ψ) = ψ)
    (hStable : ∀ ψ : State, InCode ψ → S ψ = ψ) :
    ∀ ψ : State, InCode ψ → S (R (E ψ)) = ψ := by
  intro ψ
  intro F
  have hB := hRecover ψ F
  have hC := hStable ψ F
  rw [hB]
  exact hC

example (State : Type) (ψ : State)
    (E1 E2 R : State → State)
    (h1 : R (E1 ψ) = ψ)
    (h2 : R (E2 ψ) = ψ) :
    ∀ φ : State,
      (φ = E1 ψ ∨ φ = E2 ψ) → R φ = ψ := by
  intro φ F
  cases F with
   | inl F1 =>
   rw [F1]
   exact h1
   |  inr F2 =>
    rw [F2]
    exact h2

example (State : Type)
    (InCode : State → Prop)
    (E1 E2 R : State → State)
    (h1 : ∀ ψ : State, InCode ψ → R (E1 ψ) = ψ)
    (h2 : ∀ ψ : State, InCode ψ → R (E2 ψ) = ψ) :
    ∀ ψ φ : State, InCode ψ →
      (φ = E1 ψ ∨ φ = E2 ψ) → R φ = ψ := by
    intro ψ φ hCode hError
    have blah := h1 ψ hCode
    have blahblah := h2 ψ hCode
    cases hError with
     | inl F1 =>
    rw [F1]
    exact blah
     | inr F2 =>
     rw [F2]
     exact blahblah


  example (State : Type)
    (InCode : State → Prop)
    (E R S : State → State)
    (hRecover : ∀ ψ : State, InCode ψ → R (E ψ) = ψ)
    (hStable : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    S (R (E ψ)) = ψ := by
   rw [hRecover ψ hCode]
   exact hStable ψ hCode

   example (State : Type) (ψ φ : State)
    (E1 E2 R S : State → State)
    (h1 : R (E1 ψ) = ψ)
    (h2 : R (E2 ψ) = ψ)
    (hStable : S ψ = ψ)
    (hError : φ = E1 ψ ∨ φ = E2 ψ) :
    S (R φ) = ψ := by
    cases hError with
      | inl F1 =>
      rw [F1]
      rw [h1]
      exact hStable
      | inr F2 =>
      rw [F2]
      rw [h2]
      exact hStable

  example (State : Type) (ψ φ : State)
    (E1 E2 R S : State → State)
    (h1 : R (E1 ψ) = ψ)
    (h2 : R (E2 ψ) = ψ)
    (hStable : S ψ = ψ)
    (hError : φ = E1 ψ ∨ φ = E2 ψ) :
    S (R φ) = ψ := by
     have hRecovered : R φ = ψ := by
      cases hError with
        | inl F1 =>
          rw [F1]
          exact h1
        | inr F2 =>
          rw [F2]
          exact h2
     rw [hRecovered]
     exact hStable
  example (State : Type)
    (InCode : State → Prop)
    (E S : State → State)
    (hPreserve : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (hStable : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    S (E ψ) = E ψ := by
   have hNew : InCode (E ψ) := by
     exact hPreserve ψ hCode
   exact hStable (E ψ) hNew

 example (State : Type)
    (InCode : State → Prop)
    (E : State → State)
    (hPreserve : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (ψ : State)
    (hCode : InCode ψ) :
    InCode (E (E ψ)) := by
    have hNew : InCode (E ψ) := by
     exact hPreserve ψ hCode
    exact hPreserve (E ψ) hNew

example (State : Type)
    (InCode : State → Prop)
    (E F S : State → State)
    (hE : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (hF : ∀ ψ : State, InCode ψ → InCode (F ψ))
    (hS : ∀ ψ : State, InCode ψ → S ψ = ψ)
    (ψ : State)
    (hCode : InCode ψ) :
    S (F (E ψ)) = F (E ψ) := by
     have hEpsi : InCode (E ψ) := by
      exact hE ψ hCode
     have hEEpsi : InCode (F (E ψ)) := by
      exact hF (E ψ) hEpsi
     exact hS (F (E ψ)) hEEpsi

example (State : Type)
    (S E : State → State)
    (ψ : State)
    (hStable : S ψ = ψ)
    (hComm : ∀ φ : State, S (E φ) = E (S φ)) :
    S (E ψ) = E ψ := by
    rw [hComm ψ]
    rw [hStable]

example (State : Type)
    (S T E : State → State)
    (ψ : State)
    (hS : S ψ = ψ)
    (hT : T ψ = ψ)
    (hCommS : ∀ φ : State, S (E φ) = E (S φ))
    (hCommT : ∀ φ : State, T (E φ) = E (T φ)) :
    S (E ψ) = E ψ ∧ T (E ψ) = E ψ := by
    constructor
    rw [hCommS ψ]
    rw [hS]
    rw [hCommT ψ]
    rw [hT]

example (State : Type)
    (S T E : State → State)
    (hCommS : ∀ φ : State, S (E φ) = E (S φ))
    (hCommT : ∀ φ : State, T (E φ) = E (T φ)) :
    ∀ ψ : State,
      (S ψ = ψ ∧ T ψ = ψ) →
      (S (E ψ) = E ψ ∧ T (E ψ) = E ψ) := by
    intro ψ L
    constructor
    rw [hCommS ψ]
    rw [L.1]
    rw [hCommT ψ]
    rw [L.2]

example (State Index : Type)
    (S : Index → State → State)
    (E : State → State)
    (ψ : State)
    (hCode : ∀ i : Index, S i ψ = ψ)
    (hComm : ∀ (i : Index) (φ : State),
      S i (E φ) = E (S i φ)) :
    ∀ i : Index, S i (E ψ) = E ψ := by
    intro i
    rw [hComm i ψ]
    rw [hCode]

example (State Index : Type)
    (S : Index → State → State)
    (E : State → State)
    (hComm : ∀ (i : Index) (φ : State),
      S i (E φ) = E (S i φ)) :
    ∀ ψ : State,
      (∀ i : Index, S i ψ = ψ) →
      (∀ i : Index, S i (E ψ) = E ψ) := by
    intro ψ
    intro assu
    intro i
    rw [hComm i ψ]
    rw [assu]

     def InStabilizerCode {State Index : Type}
    (S : Index → State → State) (ψ : State) : Prop :=
  ∀ i : Index, S i ψ = ψ

example (State Index : Type)
    (S : Index → State → State)
    (E : State → State)
    (hComm : ∀ (i : Index) (φ : State),
      S i (E φ) = E (S i φ))
    (ψ : State)
    (hCode : InStabilizerCode S ψ) :
    InStabilizerCode S (E ψ) := by
    unfold InStabilizerCode at hCode ⊢
    intro i
    rw [hComm i ψ]
    rw [hCode i]


example (State : Type)
    (InCode : State → Prop)
    (E F : State → State)
    (hE : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (hF : ∀ ψ : State, InCode ψ → InCode (F ψ)) :
    ∀ ψ : State, InCode ψ → InCode (F (E ψ)) := by
   intro ψ
   intro assu
   have hEpsi : InCode (E ψ) := by
    exact hE ψ assu
   exact hF (E ψ) hEpsi

theorem preserve_twice (State : Type)
    (InCode : State → Prop)
    (E F : State → State)
    (hE : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (hF : ∀ ψ : State, InCode ψ → InCode (F ψ)) :
    ∀ ψ : State, InCode ψ → InCode (F (E ψ)) := by
  intro ψ
  intro assu
  have hEpsi : InCode (E ψ) := by
    exact hE ψ assu
  exact hF (E ψ) hEpsi
#check preserve_twice

example (State : Type)
    (InCode : State → Prop)
    (E : State → State)
    (hE : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (ψ : State)
    (hCode : InCode ψ) :
    InCode (E (E ψ)) := by
        exact preserve_twice State InCode E E hE hE ψ hCode


example (State : Type)
    (InCode : State → Prop)
    (E F G : State → State)
    (hE : ∀ ψ : State, InCode ψ → InCode (E ψ))
    (hF : ∀ ψ : State, InCode ψ → InCode (F ψ))
    (hG : ∀ ψ : State, InCode ψ → InCode (G ψ))
    (ψ : State)
    (hCode : InCode ψ) :
    InCode (G (F (E ψ))) := by
    have hEpsi : InCode (E ψ) := by
     exact hE ψ hCode
    have hFEpsi : InCode (F (E (ψ))) := by
     exact preserve_twice State InCode E F hE hF ψ hCode
    exact hG (F (E ψ)) hFEpsi

example : ∃ n : ℕ, n + 2 = 5 := by
  use 3

example : ∃ n : ℕ, n + 4 = 10 := by
  use 6

example : ∃ n : ℕ, n + 2 = 7 ∧ n + 3 = 8 := by
  use 5

example (a : ℕ) : ∃ n : ℕ, n = a + 1 := by
  use a + 1

example : ∃ a b : ℕ, a + b = 10 ∧ a = b := by
  use 5 , 5
example (h : ∃ n : ℕ, n + 2 = 7) :
    ∃ n : ℕ, n + 2 = 7 ∨ n + 2 = 8 := by
  obtain ⟨n, hn⟩ := h
  use n
  left
  exact hn

example (h : ∃ n : ℕ, n + 2 = 7 ∧ n + 3 = 8) :
    ∃ n : ℕ, n + 3 = 8 := by
   obtain ⟨n, hn⟩ := h
   use n
   exact hn.right

example (h : ∃ n : ℕ, n + 2 = 7 ∧ n + 3 = 8) :
    ∃ n : ℕ, n + 3 = 8 ∧ n + 2 = 7 := by
  obtain ⟨ n, hn⟩ :=h
  use n
  constructor
  exact hn.right
  exact hn.left


example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n)
    (hPQ : ∀ n : ℕ, P n → Q n) :
    ∃ n : ℕ, Q n := by
     obtain ⟨ n, hn⟩ :=h
     use n
     exact hPQ n hn

example (P Q R : ℕ → Prop)
    (h : ∃ n : ℕ, P n ∨ Q n)
    (hPR : ∀ n : ℕ, P n → R n)
    (hQR : ∀ n : ℕ, Q n → R n) :
    ∃ n : ℕ, R n := by
   obtain ⟨ n, hn⟩ :=h
   use n
   cases hn with
     | inl F1 =>
       exact hPR n F1
     | inr F2 =>
       exact hQR n F2

example (P Q : ℕ → Prop)
    (hP : ∃ n : ℕ, P n)
    (hQ : ∃ m : ℕ, Q m) :
    ∃ n m : ℕ, P n ∧ Q m := by
   obtain ⟨ n, hn⟩ :=hP
   obtain ⟨ m, hm⟩ :=hQ
   use n
   use m

example (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b

example (State : Type)
    (InCode : State → Prop)
    (S : State → State)
    (hS : ∀ ψ, InCode ψ → S ψ = ψ)
    (ψ : State)
    (hψ : InCode ψ) :
    S ψ = ψ := by
  exact hS ψ hψ

example (State : Type)
    (InCode : State → Prop)
    (S T : State → State)
    (hS : ∀ ψ, InCode ψ → S ψ = ψ)
    (hT : ∀ ψ, InCode ψ → T ψ = ψ)
    (ψ : State)
    (hψ : InCode ψ) :
    S (T ψ) = ψ := by
  rw [hT ψ hψ]
  rw [hS ψ hψ]

example (State : Type)
    (InCode : State → Prop)
    (S T : State → State)
    (hS : ∀ ψ, InCode ψ → S ψ = ψ)
    (hT : ∀ ψ, InCode ψ → T ψ = ψ) :
    ∀ ψ, InCode ψ → S (T ψ) = ψ := by
  intro ψ
  intro hψ
  rw [hT ψ hψ]
  rw [hS ψ hψ]

example (State : Type)
    (S T : State → State)
    (ψ : State)
    (hψ : S ψ = ψ ∧ T ψ = ψ) :
    S (T ψ) = ψ := by
  rw [hψ.2]
  exact hψ.1

example (State : Type)
    (S : State → State)
    (ψ : State)
    (hS : S ψ = ψ) :
    S (S ψ) = ψ := by
  rw [hS]
  exact hS

def InStabffilizerCode {State : Type}
    (S T : State → State) (ψ : State) : Prop :=
  S ψ = ψ ∧ T ψ = ψ

example (State : Type) (S T : State → State)
    (ψ : State) (hψ : InStabffilizerCode S T ψ) :
    T ψ = ψ := by
     exact hψ.2


example (State : Type) (S T : State → State)
    (ψ : State)
    (hS : S ψ = ψ)
    (hT : T ψ = ψ) :
    InStabffilizerCode S T ψ := by
      unfold InStabffilizerCode
      constructor
      exact hS
      exact hT

example (State : Type) (S T : State → State)
    (ψ : State) (hψ : InStabffilizerCode S T ψ) :
    InStabffilizerCode T S ψ := by
    unfold InStabffilizerCode
    constructor
    exact hψ.2
    exact hψ.1

example (State : Type) (S T : State → State)
    (ψ : State) (hψ : InStabffilizerCode S T ψ) :
    S (T ψ) = ψ := by
    rw [hψ.2]
    exact hψ.1

example (State : Type) (S T : State → State) :
    ∀ ψ, InStabffilizerCode S T ψ →
      (S (T ψ) = ψ ∧ T (S ψ) = ψ) := by

    intro ψ hψ
    constructor
    rw [hψ.2]
    exact hψ.1
    rw [hψ.1]
    exact hψ.2

example (d : ℕ) (hd : 3 ≤ d) :
    1 ≤ (d - 1) / 2 := by
  omega

example (n d : ℕ)
    (hSentinel : d = n + 1)
    (hBound : d ≤ n) :
    False := by
    --obviously true
  omega

example (n d : ℕ) (EmptyErrors : Prop)
    (hEmpty : EmptyErrors → d = n + 1)
    (hBound : d ≤ n) :
    ¬ EmptyErrors := by
  intro hE
  have hD : d = n + 1 := hEmpty hE
  omega

example (n d : ℕ) (EmptyErrors A B : Prop)
    (hEmpty : EmptyErrors → d = n + 1)
    (hA : A → d ≤ n)
    (hB : B → d ≤ n)
    (hEither : A ∨ B) :
    ¬ EmptyErrors := by
  intro hE
  have hD : d = n + 1 := hEmpty hE
  cases hEither with
  | inl F1 =>
      have hbbb : d ≤ n := hA F1
      omega
  | inr F2 =>
      have hccc : d ≤ n := hB F2
      omega

example (d : ℕ) (GoodCode : Prop)
    (hDistance : GoodCode → 5 ≤ d) :
    GoodCode → 2 ≤ (d - 1) / 2 := by
  intro F
  have hF: 5 ≤ d := hDistance F
  omega

example (d : ℕ) (GoodCode : Prop)
    (hDistance : GoodCode → 7 ≤ d) :
    GoodCode → 3 ≤ (d - 1) / 2 := by
  intro gf
  have hgf : 7 ≤ d := hDistance gf
  omega

example (d : ℕ) (A B : Prop)
    (hA : A → 5 ≤ d)
    (hB : B → 7 ≤ d)
    (hEither : A ∨ B) :
    2 ≤ (d - 1) / 2 := by
  cases hEither with
  | inl F1 =>
      have hhA : 5 ≤ d := hA F1
      omega
  | inr F2 =>
      have hhB : 7 ≤ d := hB F2
      omega

example (n : ℕ)
    (h : ∃ d : ℕ, 5 ≤ d ∧ d ≤ n) :
    ∃ d : ℕ, d ≤ n ∧ 2 ≤ (d - 1) / 2 := by
  obtain ⟨d, hd⟩ := h
  use d
  constructor
  · exact hd.2
  · have hhd : 5 ≤ d := hd.1
    omega

example (State : Type) (ψ : State)
    (E R S : State → State)
    (hRecover : R (E ψ) = ψ)
    (hFix : S ψ = ψ) :
    S (R (E ψ)) = ψ := by
  rw [hRecover]
  exact hFix

example (A B C : Prop)
    (h : A ∨ B)
    (hAC : A → C)
    (hBC : B → C) : C := by
  cases h with
  | inl F1 =>
      let L := hAC F1
      exact L
  | inr F2 =>
      let M := hBC F2
      exact M

example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n ∧ Q n) :
    ∃ n : ℕ, Q n := by
  obtain ⟨n, hn⟩ := h
  use n
  exact hn.2

example (P Q : Prop) (hPQ : P → Q) :
    P → (Q ∧ P) := by
  intro hP
  let M := hPQ hP
  constructor
  · exact M
  · exact hP

example (State : Type) (E : State → State)
    (hEE : ∀ ψ : State, E (E ψ) = ψ)
    (ψ : State) :
    E (E (E ψ)) = E ψ := by
  rw [hEE ψ]

example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n)
    (hRule : ∀ n : ℕ, P n → Q (n + 1)) :
    ∃ m : ℕ, Q m := by
  obtain ⟨n, hn⟩ := h
  have hhA : Q (n + 1) := hRule n hn
  use n + 1

example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n)
    (hRule : ∀ n : ℕ, P n → Q n) :
    ∃ n : ℕ, P n ∧ Q n := by
   obtain ⟨ n, hn⟩ := h
   use n
   constructor
   exact hn
   exact hRule n hn

example {State : Type} (E R : State → State)
    (ψ : State) (hRecover : R (E ψ) = ψ) :
    E (R (E ψ)) = E ψ := by
   rw [hRecover]

example (A B : Prop)
    (hEither : A ∨ B)
    (hNotA : ¬ A) : B := by
    cases hEither with
     | inl hA =>
      exfalso
      exact hNotA hA
     |  inr hB =>
      exact hB

example (n : ℕ)
    (hLow : 4 ≤ n) (hHigh : n ≤ 6)
    (hNotFour : n ≠ 4) (hNotSix : n ≠ 6) :
    n = 5 := by
    omega


example (n : ℕ) (A B : Prop)
    (hEither : A ∨ B)
    (hA : A → 5 ≤ n)
    (hB : B → 8 ≤ n) :
    5 ≤ n := by
    cases hEither with
      | inl hhA =>
      have hhhA: 5 ≤ n := hA hhA
      exact hhhA
      | inr hhB =>
        have hhhB: 8 ≤ n := hB hhB
        omega

example (P Q : ℕ → Prop)
    (h : ∃ n : ℕ, P n)
    (hDouble : ∀ n : ℕ, P n → Q (2 * n)) :
    ∃ m : ℕ, Q m := by
   obtain ⟨ n, hn⟩ := h
   have hhd: Q (2 * n) := hDouble n hn
   let m := 2 * n
   use m

example {State : Type} (E F G : State → State)
    (ψ : State) (hUndo : ∀ φ, F (E φ) = φ) :
    G (F (E ψ)) = G ψ := by
    rw [hUndo]

example (A B C : Prop)
    (hAB : A → B) (hAC : A → C) :
    A → (B ∧ C) := by
  intro hA
  constructor
  exact hAB hA
  exact hAC hA

example : (Qubit.X * Qubit.H) * Qubit.H = Qubit.X := by
  rw [mul_assoc]
  rw [Qubit.H_sq]
  rw [mul_one]

example :
    (Qubit.T * Qubit.T) * (Qubit.T * Qubit.T) = Qubit.Z := by
  rw [Qubit.T_sq]
  rw [Qubit.S_sq]


example :
    ((Qubit.T * Qubit.T) * (Qubit.T * Qubit.T)) * Qubit.Z = 1 := by
    rw [Qubit.T_sq]
    rw [Qubit.S_sq]
    rw [Qubit.Z_sq]


example :
    (Qubit.H * (Qubit.X * Qubit.X)) * Qubit.H = 1 := by
   rw [Qubit.X_sq]
   rw [mul_one]
   rw [Qubit.H_sq]

example {State : Type}
    (S T : State → State) (ψ : State)
    (hS : S ψ = ψ) (hT : T ψ = ψ) :
    S (T ψ) = ψ := by
  rw [hT]
  exact hS

example {State : Type}
    (S E : State → State) (ψ : State)
    (hS : S ψ = ψ)
    (hComm : ∀ φ, S (E φ) = E (S φ)) :
    S (E ψ) = E ψ := by
   rw [hComm ψ]
   rw [hS]

example {State : Type}
    (S T E : State → State) (ψ : State)
    (hS : S ψ = ψ) (hT : T ψ = ψ)
    (hSE : ∀ φ, S (E φ) = E (S φ))
    (hTE : ∀ φ, T (E φ) = E (T φ)) :
    S (E ψ) = E ψ ∧ T (E ψ) = E ψ := by
    constructor
    rw [hSE ψ]
    rw [hS]
    rw [hTE ψ]
    rw [hT]

example {State Index : Type}
    (S : Index → State → State)
    (E : State → State) (ψ : State)
    (hFixed : ∀ i, S i ψ = ψ)
    (hComm : ∀ i φ, S i (E φ) = E (S i φ)) :
    ∀ i, S i (E ψ) = E ψ := by
  intro i
  rw [hComm i ψ]
  rw [hFixed]

example {State : Type}
    (S T : State → State) (ψ : State)
    (hS : S ψ = ψ) (hT : T ψ = ψ) :
    S (T ψ) = ψ := by
  calc
    S (T ψ) = S ψ := by
      rw [hT]
    _ = ψ := by
      exact hS


example {State : Type}
    (S E : State → State) (ψ : State)
    (hS : S ψ = ψ)
    (hComm : ∀ φ, S (E φ) = E (S φ)) :
    S (E ψ) = E ψ := by
  calc
    S (E ψ) = E (S ψ) := by
      rw [hComm ψ]
    _ = E ψ := by
      rw [hS]


example {State : Type}
    (S T U : State → State) (ψ : State)
    (hS : S ψ = ψ)
    (hT : T ψ = ψ)
    (hU : U ψ = ψ) :
    S (T (U ψ)) = ψ := by
  rw [hU]
  rw [hT]
  rw [hS]

example {State : Type} (E : State → State)
    (hE : ∀ ψ, E (E ψ) = ψ) :
    (fun ψ => E (E ψ)) = (fun ψ => ψ) := by
  funext ψ
  exact hE ψ

example {State : Type} (S E : State → State)
    (hComm : ∀ ψ, S (E ψ) = E (S ψ)) :
    (fun ψ => S (E ψ)) = (fun ψ => E (S ψ)) := by
  funext ψ
  exact hComm ψ

example {State : Type} (S E : State → State)
    (hUndo : ∀ ψ, E (E ψ) = ψ) :
    (fun ψ => S (E (E ψ))) = S := by
  funext ψ
  rw [hUndo]

example (f g : ℕ → ℕ → ℕ)
    (h : ∀ a b, f a b = g a b) :
    f = g := by
  funext a b
  exact h a b

example :
    (fun a b : ℕ => a + b) = (fun a b : ℕ => b + a) := by
  funext a b
  rw [Nat.add_comm]

example {State : Type} (E F : State → State)
    (hE : ∀ ψ, E (E ψ) = ψ)
    (hF : ∀ ψ, F (F ψ) = ψ) :
    (fun ψ => E (F (F (E ψ)))) = (fun ψ => ψ) := by
  funext ψ
  rw [hF (E ψ)]
  rw [hE (ψ)]
