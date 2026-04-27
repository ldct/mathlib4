/-
# Investigation: Can `push` be used for computing derivatives?

## Summary of findings

### Which deriv lemmas fit the push pattern?

The `push` tactic rewrites by "pushing" a constant deeper into an expression. For `deriv`,
we want lemmas of the form `deriv (compound_expr) x = ... (deriv simpler_expr x) ...`.

**Clean fits (no differentiability side conditions):**
1. `deriv.neg` : `deriv (-f) x = -deriv f x` -- unconditional
2. `deriv_const_mul_field` : `deriv (fun y => u * v y) x = u * deriv v x` -- unconditional
   (only for field-valued functions, uses the fact that scalar mult by a field element
   preserves differentiability or maps to 0)
3. `deriv_mul_const_field` : `deriv (fun x => u x * v) x = deriv u x * v` -- unconditional

**Lemmas that fit the pattern but have differentiability side conditions:**
4. `deriv_add` : `deriv (f + g) x = deriv f x + deriv g x`
   -- requires `DifferentiableAt 𝕜 f x` and `DifferentiableAt 𝕜 g x`
5. `deriv_sub` : `deriv (f - g) x = deriv f x - deriv g x`
   -- requires `DifferentiableAt 𝕜 f x` and `DifferentiableAt 𝕜 g x`
6. `deriv_const_smul` : `deriv (c • f) x = c • deriv f x`
   -- requires `DifferentiableAt 𝕜 f x`
7. `deriv_const_mul` : `deriv (fun y => c * d y) x = c * deriv d x`
   -- requires `DifferentiableAt 𝕜 d x`
8. `deriv_sum` : `deriv (∑ i ∈ u, A i) x = ∑ i ∈ u, deriv (A i) x`
   -- requires `∀ i ∈ u, DifferentiableAt 𝕜 (A i) x`

**Non-linear rules that ALSO work with push:**
The push mechanism doesn't require the RHS to have a distributional form.
Any lemma with `deriv` at the head of the LHS works. These include:
9. Product rule: `deriv (f * g) x = deriv f x * g x + f x * deriv g x`
10. Chain rule: `deriv (g ∘ f) x = deriv g (f x) * deriv f x`
11. Quotient rule: `deriv (f / g) x = (deriv f x * g x - f x * deriv g x) / g x ^ 2`
12. Power rule: `deriv (f ^ n) x = n * f x ^ (n-1) * deriv f x`
13. Inverse rule: `deriv (f⁻¹) x = -deriv f x / f x ^ 2`
Push recursively applies these, so e.g. `push deriv` on `deriv ((f+g)*f)` first
applies the product rule, then applies `deriv_add` to `deriv (f+g)` in the result.

### Does `push` handle side conditions?

Yes! The `push` tactic supports a `disch` parameter:
  `push (disch := tac) deriv`
This is analogous to how `push (disch := positivity) Real.log` handles the `x ≠ 0`
conditions in `log_mul`. So we CAN tag `deriv_add` etc. with `@[push]` and use
`push (disch := fun_prop) deriv` to discharge differentiability conditions.

### Is this actually useful?

**Compared to `simp`**: The lemmas `deriv_add`, `deriv_sub`, `deriv.neg` etc. are already
tagged `@[simp]`. So `simp [deriv_add, deriv_sub, ...]` already works for these. The `push`
approach would be slightly more targeted (only applying deriv-related rewrites).

**Conclusion**: `push (disch := fun_prop) deriv` can fully compute symbolic derivatives.
It handles both linear rules (addition, subtraction, scalar multiplication) AND non-linear
rules (product rule, chain rule, power rule, quotient rule, inverse rule). The push
mechanism recursively applies rules, so compound expressions are fully expanded.

### fderiv considerations

The Frechet derivative `fderiv` has parallel lemmas:
- `fderiv_neg` : unconditional, clean push pattern
- `fderiv_add` : conditional on differentiability
- `fderiv_sub` : conditional on differentiability
The same analysis applies. The key difference is that `fderiv` returns a continuous
linear map, so the algebra is slightly different, but the push/pull structure is the same.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Push
import Mathlib.Tactic.FunProp

private axiom test_sorry : forall {α}, α

/-! ## Tag unconditional deriv lemmas with @[push] -/

-- `deriv.neg` has no side conditions: `deriv (-f) x = -deriv f x`
attribute [push] deriv.neg

-- `deriv_const_mul_field` has no side conditions for field-valued functions:
-- `deriv (fun y => u * v y) x = u * deriv v x`
attribute [push] deriv_const_mul_field

-- `deriv_mul_const_field` has no side conditions for field-valued functions:
-- `deriv (fun x => u x * v) x = deriv u x * v`
attribute [push] deriv_mul_const_field

/-! ## Tag conditional deriv lemmas with @[push] -/

-- These require differentiability side conditions, which can be discharged by `fun_prop`.
attribute [push] deriv_add
attribute [push] deriv_sub
attribute [push] deriv_const_smul

/-! ## Test: unconditional lemmas (no discharger needed) -/

section unconditional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f g : 𝕜 → 𝕜} {x : 𝕜}

-- push deriv through negation (no side conditions needed)
example (h : deriv (-f) x = 0) : -deriv f x = 0 := by
  push deriv at h
  exact h

-- push deriv through constant multiplication (field case, no side conditions)
example (c : 𝕜) (h : deriv (fun y => c * f y) x = 0) : c * deriv f x = 0 := by
  push deriv at h
  exact h

-- push deriv through multiplication by constant on the right (field case)
example (c : 𝕜) (h : deriv (fun y => f y * c) x = 0) : deriv f x * c = 0 := by
  push deriv at h
  exact h

end unconditional

/-! ## Test: conditional lemmas (need discharger for differentiability) -/

section conditional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : 𝕜 → F} {x : 𝕜}

-- push deriv through addition (needs differentiability discharged)
example (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    (h : deriv (f + g) x = 0) : deriv f x + deriv g x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

-- push deriv through subtraction
example (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    (h : deriv (f - g) x = 0) : deriv f x - deriv g x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

-- push deriv through scalar multiplication
example {R : Type*} [NontriviallyNormedField R] [NormedAlgebra 𝕜 R]
    [NormedSpace R F] [IsScalarTower 𝕜 R F]
    (c : R) (hf : DifferentiableAt 𝕜 f x)
    (h : deriv (c • f) x = 0) : c • deriv f x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

end conditional

/-! ## Test: combined example -/

section combined

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f g h : 𝕜 → 𝕜} {x : 𝕜}

-- A more complex expression combining negation and field multiplication
-- push should handle nested applications
example (c : 𝕜) (hyp : deriv (fun y => c * (-f) y) x = 0) : c * -deriv f x = 0 := by
  push deriv at hyp
  exact hyp

end combined

/-! ## Non-linear rules: product rule, chain rule, etc.

These DO work with push, even though the RHS doesn't have the "clean" distributional form.
The push mechanism just rewrites any lemma with the target constant at the head of the LHS.
-/

attribute [push] deriv_mul
attribute [push] deriv_comp
attribute [push] deriv_inv''
attribute [push] deriv_div
attribute [push] deriv_pow

section product_rule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f g : 𝕜 → 𝕜} {x : 𝕜}

-- Product rule: deriv (f * g) = f' * g + f * g'
example (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    (h : deriv (f * g) x = 0) : deriv f x * g x + f x * deriv g x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

end product_rule

section chain_rule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f g : 𝕜 → 𝕜} {x : 𝕜}

-- Chain rule: deriv (g ∘ f) = g'(f(x)) * f'(x)
example (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x)
    (h : deriv (g ∘ f) x = 0) : deriv g (f x) * deriv f x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

end chain_rule

section power_rule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f : 𝕜 → 𝕜} {x : 𝕜}

-- Power rule: deriv (f ^ n) = n * f^(n-1) * f'
example (hf : DifferentiableAt 𝕜 f x) (n : ℕ)
    (h : deriv (f ^ n) x = 0) : ↑n * f x ^ (n - 1) * deriv f x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

end power_rule

section inverse_rule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f : 𝕜 → 𝕜} {x : 𝕜}

-- Inverse rule: deriv (f⁻¹) = -f' / f²
example (hf : DifferentiableAt 𝕜 f x) (hfx : f x ≠ 0)
    (h : deriv (f⁻¹) x = 0) : -deriv f x / f x ^ 2 = 0 := by
  push (disch := first | fun_prop | assumption) deriv at h
  exact h

end inverse_rule

section compound

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f g : 𝕜 → 𝕜} {x : 𝕜}

-- Compound: push deriv through (f + g) * f, applying both addition and product rules
-- push applies deriv_mul, then recursively applies deriv_add inside the result
example (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    (h : deriv ((f + g) * f) x = 0) :
    (deriv f x + deriv g x) * f x + (f + g) x * deriv f x = 0 := by
  push (disch := fun_prop) deriv at h
  exact h

end compound
