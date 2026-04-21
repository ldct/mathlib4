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

**Lemmas that do NOT fit the push pattern at all:**
9. Product rule: `deriv (f * g) x = deriv f x * g x + f x * deriv g x`
   -- The RHS has a fundamentally different structure (sum of products)
10. Chain rule: `deriv (g ∘ f) x = deriv f x • deriv g (f x)`
    -- The RHS involves evaluating `deriv g` at `f x`, not at `x`
11. Quotient rule: `deriv (f / g) x = (deriv f x * g x - f x * deriv g x) / g x ^ 2`
    -- Complex RHS structure
12. Power rule: `deriv (fun x => f x ^ n) x = ...`
    -- Uses chain rule internally

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

**The real limitation**: For practical derivative computation, you almost always need the
chain rule and product rule, which do NOT fit the push pattern. So `push deriv` would only
handle the "linear" part of differentiation. A dedicated `deriv` tactic (or `simp` with
the right lemma set) would be more practical.

**Conclusion**: Tagging the unconditional lemmas (`deriv.neg`, `deriv_const_mul_field`)
with `@[push]` is harmless and works. Tagging the conditional ones (`deriv_add`, etc.)
also works when combined with `disch := fun_prop`. But this covers only the linear
fragment of differentiation, making it of limited practical value.

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

/-! ## Demonstration: what does NOT work with push

The product rule does NOT fit the push pattern because:
  deriv (f * g) x = deriv f x * g x + f x * deriv g x
The RHS is not of the form `op (deriv f x) (deriv g x)`.

The chain rule does NOT fit the push pattern because:
  deriv (g ∘ f) x = deriv f x • deriv g (f x)
The RHS involves `deriv g` evaluated at `f x`, not at `x`.

These are fundamental limitations: `push` can only handle the LINEAR
fragment of differentiation (where deriv distributes cleanly).
-/
