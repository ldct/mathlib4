module
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Domain

private axiom test_sorry : ∀ {α}, α

section logic

variable {p q r : Prop}

/-- info: (q ∧ (p ∨ q)) ∧ r ∧ (p ∨ r) -/
#guard_msgs in
#push _ ∨ _ => False ∧ p ∨ q ∧ r

/-- info: (p ∨ q) ∧ (p ∨ r) -/
#guard_msgs in
#push _ ∨ _ => (p ∨ q) ∧ (p ∨ r)

/-- info: (p ∧ q ∨ q) ∨ p ∧ r ∨ r -/
#guard_msgs in
#push _ ∧ _ => (p ∨ True) ∧ (q ∨ r)

example {r : ℕ → Prop} : ∀ n : ℕ, p ∨ r n ∧ q ∧ n = 1 := by
  push ∀ n, _
  guard_target =ₛ p ∨ (∀ n, r n) ∧ q ∧ ∀ n : ℕ, n = 1
  pull ∀ n, _
  guard_target =ₛ ∀ n : ℕ, p ∨ r n ∧ q ∧ n = 1
  exact test_sorry

example {r : ℕ → Prop} : ∃ n : ℕ, p ∨ r n ∨ q ∧ n = 1 := by
  push ∃ n, _
  guard_target =ₛ p ∨ (∃ n, r n) ∨ q ∧ True
  -- the lemmas `exists_or_left`/`exist_and_left` don't exist, so they can't be tagged for `pull`
  fail_if_success pull ∃ n, _
  exact test_sorry

/-- info: p ∨ ∃ x, q ∧ x = 1 -/
#guard_msgs in
#pull ∃ _, _ => p ∨ q ∧ ∃ n : ℕ, n = 1

/--
info: DiscrTree branch for Or:
  (node
   (* => (node
     (False => (node #[or_false:1000]))
     (And => (node (* => (node (* => (node #[or_and_left:1000]))))))
     (True => (node #[or_true:1000]))))
   (False => (node (* => (node #[false_or:1000]))))
   (And => (node (* => (node (* => (node (* => (node #[and_or_right:1000]))))))))
   (True => (node (* => (node #[true_or:1000])))))
-/
#guard_msgs in
#push_discr_tree Or

end logic

section lambda

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  push fun x ↦ _
  with_reducible rfl

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  simp only [pushFun]

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  pull fun _ ↦ _
  with_reducible rfl

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  simp only [pullFun]

end lambda

section log

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.log (a * b) = Real.log a + Real.log b := by
  pull (disch := positivity) Real.log
  rfl

variable (a b c : Real) (ha : 0 < a) (hc : 0 < c)

/-- info: ↑4 * Real.log a + -Real.log c - b * Real.log a + b -/
#guard_msgs in
#push (disch := positivity) Real.log => Real.log (a ^ 4 * c⁻¹ / a ^ b * Real.exp b)

/-- info: ∑ i ∈ Finset.Ioo 0 5, Real.log ↑i -/
#guard_msgs in
#push (disch := simp <;> grind) Real.log => Real.log (∏ i ∈ Finset.Ioo 0 5, (i : Nat))

set_option pp.numericTypes true in
/-- info: Real.log (a ^ (4 : ℝ) * c⁻¹ / a ^ b) + b -/
#guard_msgs in
#pull (disch := positivity) Real.log => 4 * Real.log a + -Real.log c - b * Real.log a + b

set_option pp.numericTypes true in
/-- info: Real.log (a ^ (4 : ℕ) * c⁻¹ / a ^ b) + b -/
#guard_msgs in
#pull (disch := positivity) Real.log => (4 : Nat) * Real.log a + -Real.log c - b * Real.log a + b

end log

section membership

example (x : Nat) (A : Set Nat) : x ∈ ∅ ∪ Set.univ ∩ ({a | a = 4} \ Aᶜ) := by
  push _ ∈ _
  guard_target =ₛ (False ∨ True ∧ x = 4 ∧ ¬x ∉ A)
  exact test_sorry

example (A : Set Nat) : A ∈ 𝒫 A := by
  push _ ∈ _
  rfl

example (x y : Nat) (A B : Set Nat) : (x, y) ∈ A ×ˢ B := by
  push _ ∈ _
  -- `push _ ∈ _` can unpack the pair `(x, y)` because a specialized lemma has been tagged
  guard_target =ₛ x ∈ A ∧ y ∈ B
  exact test_sorry

example (p : Nat × Nat) (A B : Set Nat) : p ∈ A ×ˢ B := by
  push _ ∈ _
  guard_target =ₛ p.1 ∈ A ∧ p.2 ∈ B
  pull _ ∈ _
  guard_target =ₛ p ∈ A ×ˢ B
  exact test_sorry

example (p : Nat × Nat) (A : Set Nat) : p ∈ Set.diagonal Nat ∪ Set.offDiag A := by
  push _ ∈ _
  guard_target =ₛ p.1 = p.2 ∨ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2
  exact test_sorry

example (x y z : Nat) : x ∈ ({x, y, z, y, x} : Set Nat) := by
  push _ ∈ _
  guard_target =ₛ x = x ∨ x = y ∨ x = z ∨ x = y ∨ x = x
  exact test_sorry

example (x : Nat) (A B C : Set Nat) : x ∈ A ∧ ¬ x ∈ B ∨ x ∈ C := by
  pull _ ∈ _
  guard_target =ₛ x ∈ A ∩ Bᶜ ∪ C
  exact test_sorry

example (a b c : α) (s : Set α) : a ∈ (∅ ∪ (Set.univ ∩ (({b, c} \ sᶜᶜ) ∪ {b | b = a}))) := by
  push _ ∈ _
  guard_target =ₛ False ∨ True ∧ ((a = b ∨ a = c) ∧ ¬¬a ∉ s ∨ a = a)
  exact test_sorry

end membership

section degree

open Polynomial

-- degree_neg, natDegree_neg, leadingCoeff_neg
example (p : ℤ[X]) : degree (-p) = degree p := by
  push Polynomial.degree
  rfl

example (p : ℤ[X]) : natDegree (-p) = natDegree p := by
  push Polynomial.natDegree
  rfl

example (p : ℤ[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  push Polynomial.leadingCoeff
  rfl

-- degree_mul, natDegree_mul, leadingCoeff_mul (NoZeroDivisors / domain)
example (p q : ℤ[X]) : degree (p * q) = degree p + degree q := by
  push Polynomial.degree
  rfl

example (p q : ℤ[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q := by
  push (disch := assumption) Polynomial.natDegree
  rfl

example (p q : ℤ[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  push Polynomial.leadingCoeff
  rfl

-- degree_pow, natDegree_pow, leadingCoeff_pow
example (p : ℤ[X]) (n : ℕ) : degree (p ^ n) = n • degree p := by
  push Polynomial.degree
  rfl

example (p : ℤ[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p := by
  push Polynomial.natDegree
  rfl

example (p : ℤ[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n := by
  push Polynomial.leadingCoeff
  rfl

-- degree_prod, natDegree_prod, leadingCoeff_prod
example (s : Finset ℕ) (f : ℕ → ℤ[X]) :
    (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := by
  push Polynomial.degree
  rfl

example (s : Finset ℕ) (f : ℕ → ℤ[X]) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  push (disch := assumption) Polynomial.natDegree
  rfl

example (s : Finset ℕ) (f : ℕ → ℤ[X]) :
    (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  push Polynomial.leadingCoeff
  rfl

end degree
