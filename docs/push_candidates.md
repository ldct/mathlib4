# Candidates for `@[push]` tagging in Mathlib

This document catalogs mathlib lemmas that follow the `@[push]` pattern:
equalities of the form `outer (inner a b) = ...` where `outer` is pushed
through `inner`. These are candidates for tagging with `@[push]` to enable
the `push` tactic.

## Already tagged

The following operations already have `@[push]` tags:

- **Negation** (`push_neg`): `Not` through `∀`, `∃`, `→`, `∧`, `∨`, `≤`, `<`, etc.
- **Membership** (`push _ ∈ _`): `∈` through `∪`, `∩`, `ᶜ`, `\`, `{a, b}`, etc.
- **Log** (`push Real.log`): `log_mul`, `log_inv`, `log_div`, `log_pow`, `log_zpow`, `log_prod`, `log_abs`
- **Floor** (`push Int.floor` / `push Nat.floor`): `floor_add_intCast`, `floor_add_natCast`, `floor_add_one`, etc.

## Tagged in companion PRs

- **Abs** (`push abs`): `abs_mul`, `abs_pow`, `abs_inv`, `abs_div`, `abs_zpow`, `abs_neg`, `abs_mul_self`
- **Star** (`push star`): `star_pow`, `star_inv`, `star_zpow`, `star_div`, `star_neg`, `star_sub`, `star_prod`, `star_sum`
- **Norm/NNNorm** (`push norm` / `push nnnorm`): `norm_mul`, `norm_inv`, `norm_div`, `norm_zpow`, `norm_pow`, `norm_prod`, `norm_neg`, `norm_smul` (and nnnorm variants)
- **Exp** (`push Real.exp`): `exp_add`, `exp_neg`, `exp_sub`, `exp_sum`
- **Sqrt** (`push Real.sqrt`): `sqrt_mul`, `sqrt_inv`, `sqrt_div`
- **Det** (`push Matrix.det`): `det_mul`, `det_pow`
- **Sign** (`push Real.sign`): `sign_mul`, `sign_pow`, `sign_neg`, `sign_inv`
- **Trace** (`push Matrix.trace`): `trace_add`, `trace_neg`, `trace_sub`, `trace_smul`, `trace_sum`
- **toNNReal/toReal** (`push ENNReal.toNNReal` / `push ENNReal.toReal`): `toNNReal_mul`, `toNNReal_pow`, `toNNReal_inv`, `toNNReal_div`, `toNNReal_add`, `toNNReal_sub`, `toNNReal_prod`, `toNNReal_sum` (and toReal variants)
- **Ceil/Fract** (`push Int.ceil` / `push Int.fract`): `ceil_neg`, `ceil_add_*`, `fract_neg`, `fract_add_*`
- **Degree/NatDegree/LeadingCoeff** (`push Polynomial.degree`, etc.): `degree_mul`, `degree_neg`, `degree_pow`, `degree_prod`, `natDegree_mul`, `natDegree_neg`, `natDegree_pow`, `natDegree_prod`, `leadingCoeff_mul`, `leadingCoeff_neg`, `leadingCoeff_pow`, `leadingCoeff_prod`
- **Eval** (`push Polynomial.eval`): `eval_add`, `eval_mul`, `eval_neg`, `eval_sub`, `eval_pow`, `eval_prod`, `eval_sum`
- **Deriv** (`push deriv`): `deriv_add`, `deriv_sub`, `deriv.neg`, `deriv_const_mul_field`, `deriv_mul`, `deriv_comp`, `deriv_pow`, `deriv_inv''`, `deriv_div`

## New candidates

### Trigonometric functions

`push Real.sin`, `push Real.cos`, `push Real.tan`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `sin_add` | `sin (x + y) = sin x * cos y + cos x * sin y` | none |
| `sin_neg` | `sin (-x) = -sin x` | none |
| `sin_sub` | `sin (x - y) = sin x * cos y - cos x * sin y` | none |
| `cos_add` | `cos (x + y) = cos x * cos y - sin x * sin y` | none |
| `cos_neg` | `cos (-x) = cos x` | none |
| `cos_sub` | `cos (x - y) = cos x * cos y + sin x * sin y` | none |
| `tan_add` | `tan (x + y) = (tan x + tan y) / (1 - tan x * tan y)` | cos ≠ 0 |
| `tan_neg` | `tan (-x) = -tan x` | none |
| `tan_sub` | `tan (x - y) = (tan x - tan y) / (1 + tan x * tan y)` | cos ≠ 0 |

### Hyperbolic functions

`push Complex.sinh`, `push Complex.cosh`, `push Complex.tanh`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `sinh_add` | `sinh (x + y) = sinh x * cosh y + cosh x * sinh y` | none |
| `sinh_neg` | `sinh (-x) = -sinh x` | none |
| `sinh_sub` | `sinh (x - y) = sinh x * cosh y - cosh x * sinh y` | none |
| `cosh_add` | `cosh (x + y) = cosh x * cosh y + sinh x * sinh y` | none |
| `cosh_neg` | `cosh (-x) = cosh x` | none |
| `cosh_sub` | `cosh (x - y) = cosh x * cosh y - sinh x * sinh y` | none |
| `tanh_neg` | `tanh (-x) = -tanh x` | none |

### Complex number parts

`push Complex.re`, `push Complex.im`, `push Complex.normSq`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `re_add` | `(z + w).re = z.re + w.re` | none |
| `re_neg` | `(-z).re = -z.re` | none |
| `re_sub` | `(z - w).re = z.re - w.re` | none |
| `re_smul` | `(s • z).re = s • z.re` | none |
| `re_sum` | `(∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re` | none |
| `re_mul` | `(z * w).re = z.re * w.re - z.im * w.im` | none |
| `im_add` | `(z + w).im = z.im + w.im` | none |
| `im_neg` | `(-z).im = -z.im` | none |
| `im_sub` | `(z - w).im = z.im - w.im` | none |
| `im_smul` | `(s • z).im = s • z.im` | none |
| `im_sum` | `(∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im` | none |
| `im_mul` | `(z * w).im = z.re * w.im + z.im * w.re` | none |
| `normSq_mul` | `normSq (z * w) = normSq z * normSq w` | none |
| `normSq_neg` | `normSq (-z) = normSq z` | none |
| `normSq_inv` | `normSq z⁻¹ = (normSq z)⁻¹` | none |
| `normSq_div` | `normSq (z / w) = normSq z / normSq w` | none |
| `normSq_zpow` | `normSq (a ^ z) = normSq a ^ z` | none |

### Complex coercion

`push Complex.ofReal` (or `push RCLike.ofReal`)

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `ofReal_add` | `((r + s : ℝ) : ℂ) = ↑r + ↑s` | none |
| `ofReal_mul` | `((r * s : ℝ) : ℂ) = ↑r * ↑s` | none |
| `ofReal_neg` | `((-r : ℝ) : ℂ) = -↑r` | none |
| `ofReal_sub` | `((r - s : ℝ) : ℂ) = ↑r - ↑s` | none |
| `ofReal_div` | `((r / s : ℝ) : ℂ) = ↑r / ↑s` | none |
| `ofReal_inv` | `((r⁻¹ : ℝ) : ℂ) = (↑r)⁻¹` | none |
| `ofReal_pow` | `((r ^ n : ℝ) : ℂ) = ↑r ^ n` | none |
| `ofReal_zpow` | `((r ^ z : ℝ) : ℂ) = ↑r ^ z` | none |
| `ofReal_prod` | `((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, ↑(f i)` | none |
| `ofReal_sum` | `((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, ↑(f i)` | none |

### Power / exponent laws

`push HPow.hPow` (pushing the exponent through arithmetic)

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `pow_add` | `a ^ (m + n) = a ^ m * a ^ n` | none (monoid) |
| `pow_mul` | `a ^ (m * n) = (a ^ m) ^ n` | none (monoid) |
| `zpow_add` | `a ^ (m + n) = a ^ m * a ^ n` | `a ≠ 0` or group |
| `zpow_neg` | `a ^ (-n) = (a ^ n)⁻¹` | none (group) |
| `zpow_mul` | `a ^ (m * n) = (a ^ m) ^ n` | none |
| `zpow_sub` | `a ^ (m - n) = a ^ m * (a ^ n)⁻¹` | none (group) |
| `rpow_add` | `x ^ (y + z) = x ^ y * x ^ z` | `0 < x` or `x ≠ 0` |
| `rpow_neg` | `x ^ (-y) = (x ^ y)⁻¹` | `0 ≤ x` |
| `rpow_mul` | `x ^ (y * z) = (x ^ y) ^ z` | `0 ≤ x` |
| `rpow_sub` | `x ^ (y - z) = x ^ y / x ^ z` | `0 < x` |

### Matrix transpose / conjugate transpose

`push Matrix.transpose`, `push Matrix.conjTranspose`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `transpose_add` | `(M + N)ᵀ = Mᵀ + Nᵀ` | none |
| `transpose_neg` | `(-M)ᵀ = -Mᵀ` | none |
| `transpose_sub` | `(M - N)ᵀ = Mᵀ - Nᵀ` | none |
| `transpose_mul` | `(M * N)ᵀ = Nᵀ * Mᵀ` | none (reverses!) |
| `transpose_pow` | `(M ^ k)ᵀ = Mᵀ ^ k` | none |
| `transpose_zpow` | `(A ^ n)ᵀ = Aᵀ ^ n` | none |
| `transpose_smul` | `(c • M)ᵀ = c • Mᵀ` | none |
| `transpose_sum` | `(∑ i ∈ s, M i)ᵀ = ∑ i ∈ s, (M i)ᵀ` | none |
| `conjTranspose_add` | `(M + N)ᴴ = Mᴴ + Nᴴ` | none |
| `conjTranspose_neg` | `(-M)ᴴ = -Mᴴ` | none |
| `conjTranspose_sub` | `(M - N)ᴴ = Mᴴ - Nᴴ` | none |
| `conjTranspose_mul` | `(M * N)ᴴ = Nᴴ * Mᴴ` | none (reverses!) |
| `conjTranspose_pow` | `(M ^ k)ᴴ = Mᴴ ^ k` | none |
| `conjTranspose_zpow` | `(A ^ n)ᴴ = Aᴴ ^ n` | none |
| `conjTranspose_smul` | `(c • M)ᴴ = star c • Mᴴ` | none |
| `conjTranspose_sum` | `(∑ i ∈ s, M i)ᴴ = ∑ i ∈ s, (M i)ᴴ` | none |

### Polynomial/power series coefficients

`push Polynomial.coeff`, `push PowerSeries.coeff`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `coeff_add` | `coeff (p + q) n = coeff p n + coeff q n` | none |
| `coeff_neg` | `coeff (-p) n = -coeff p n` | none |
| `coeff_sub` | `coeff (p - q) n = coeff p n - coeff q n` | none |
| `coeff_smul` | `coeff (r • p) n = r • coeff p n` | none |
| `coeff_sum` | `coeff (∑ i ∈ s, f i) n = ∑ i ∈ s, coeff (f i) n` | none |
| `coeff_mul` | `coeff (p * q) n = ∑ x ∈ antidiagonal n, coeff p x.1 * coeff q x.2` | none |
| `coeff_pow` | `coeff (φ ^ k) n = ∑ l ∈ finsuppAntidiag (range k) n, ∏ i, coeff (l i) φ` | none |

### Algebra evaluation

`push Polynomial.aeval`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `aeval_add` | `aeval x (p + q) = aeval x p + aeval x q` | none |
| `aeval_mul` | `aeval x (p * q) = aeval x p * aeval x q` | none |
| `aeval_neg` | `aeval x (-p) = -aeval x p` | none |
| `aeval_sub` | `aeval x (p - q) = aeval x p - aeval x q` | none |
| `aeval_prod` | `aeval f (∏ i ∈ s, φ i) = ∏ i ∈ s, aeval f (φ i)` | none |
| `aeval_sum` | `aeval f (∑ i ∈ s, φ i) = ∑ i ∈ s, aeval f (φ i)` | none |

### Formal derivative (polynomial)

`push Polynomial.derivative`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `derivative_add` | `derivative (f + g) = derivative f + derivative g` | none |
| `derivative_neg` | `derivative (-f) = -derivative f` | none |
| `derivative_sub` | `derivative (f - g) = derivative f - derivative g` | none |
| `derivative_mul` | `derivative (f * g) = derivative f * g + f * derivative g` | none |
| `derivative_pow` | `derivative (p ^ n) = C n * p ^ (n-1) * derivative p` | none |
| `derivative_smul` | `derivative (s • p) = s • derivative p` | none |
| `derivative_sum` | `derivative (∑ b ∈ s, f b) = ∑ b ∈ s, derivative (f b)` | none |

### Bochner integral

`push MeasureTheory.integral` (with `disch` for integrability)

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `integral_add` | `∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ` | Integrable |
| `integral_neg` | `∫ a, -f a ∂μ = -∫ a, f a ∂μ` | none |
| `integral_sub` | `∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ` | Integrable |
| `integral_smul` | `∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ` | none |
| `integral_div` | `∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r` | none |

### Lebesgue integral

`push MeasureTheory.lintegral`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `lintegral_add` | `∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ` | Measurable |
| `lintegral_sub` | `∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ` | conditions |
| `lintegral_smul` | `f.lintegral (c • μ) = c • f.lintegral μ` | none |

### ENNReal.ofReal

`push ENNReal.ofReal`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `ofReal_add` | `ENNReal.ofReal (p + q) = ofReal p + ofReal q` | `0 ≤ p`, `0 ≤ q` |
| `ofReal_mul` | `ENNReal.ofReal (p * q) = ofReal p * ofReal q` | `0 ≤ p` |
| `ofReal_pow` | `ENNReal.ofReal (p ^ n) = ofReal p ^ n` | `0 ≤ p` |

### Order/lattice suprema and infima

`push iSup`, `push sSup`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `iSup_add` | `(⨆ i, f i) + a = ⨆ i, f i + a` | none |
| `iSup_mul` | `(⨆ i, f i) * a = ⨆ i, f i * a` | none |
| `iSup_div` | `(⨆ i, f i) / a = ⨆ i, f i / a` | none |
| `iSup_sub` | `(⨆ i, f i) - a = ⨆ i, f i - a` | none |
| `iSup_pow` | `(⨆ i, f i) ^ n = ⨆ i, f i ^ n` | none |
| `iSup_union` | `⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x` | none |
| `sSup_add` | `sSup s + a = ⨆ b ∈ s, b + a` | none |
| `sSup_mul` | `sSup s * a = ⨆ b ∈ s, b * a` | none |
| `sSup_neg` | `sSup (-s) = -sInf s` | none |
| `sSup_union` | `sSup (s ∪ t) = sSup s ⊔ sSup t` | none |

### Cardinality

`push Finset.card`, `push Nat.card`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `card_add` | `card (s + t) = card s + card t` | none |
| `card_mul` | `card (a * b) = card a * card b` | none |
| `card_inv` | `#s⁻¹ = #s` | none |
| `card_prod` | `card (α × β) = card α * card β` | none |
| `card_sum` | `card (α ⊕ β) = card α + card β` | none |
| `card_union` | `#(s ∪ t) = #s + #t - #(s ∩ t)` | none |

### Length

`push List.length`, `push Multiset.length`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `length_add` | `(s + t).length = s.length + t.length` | none |
| `length_mul` | `(a * b).length = a.length + b.length` | none |
| `length_neg` | `(-s).length = s.length` | none |
| `length_inv` | `ℓ(w⁻¹) = ℓ(w)` | none |
| `length_sub` | `(s - t).length = s.length + t.length` | none |
| `length_sum` | `(∑ i ∈ s, f i).length = ∑ i ∈ s, (f i).length` | none |

### Order duality

`push OrderDual.toDual`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `toDual_mul` | `toDual (a * b) = toDual a * toDual b` | none |
| `toDual_inv` | `toDual a⁻¹ = (toDual a)⁻¹` | none |
| `toDual_div` | `toDual (a / b) = toDual a / toDual b` | none |
| `toDual_pow` | `toDual (a ^ b) = toDual a ^ b` | none |
| `toDual_sup` | `toDual (a ⊔ b) = toDual a ⊓ toDual b` | none |
| `toDual_sdiff` | `toDual (a \ b) = toDual b ⇨ toDual a` | none |
| `toDual_symmDiff` | `toDual (a ∆ b) = toDual a ⇔ toDual b` | none |

### Conj (RCLike)

`push RCLike.conj`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `conj_div` | `conj (x / y) = conj x / conj y` | none |
| `conj_inv` | `conj x⁻¹ = (conj x)⁻¹` | none |
| `conj_smul` | `conj (r • z) = r • conj z` | none |

### Measure

`push MeasureTheory.Measure`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `measure_union` | `μ (s₁ ∪ s₂) = μ s₁ + μ s₂` | disjoint |
| `measure_compl` | `μ sᶜ = μ univ - μ s` | conditions |
| `measure_inv` | `μ A⁻¹ = μ A` | none (Haar) |

### Kernel operations

`push MeasurableSpace.ker`

| Lemma | Statement | Side conditions |
|-------|-----------|-----------------|
| `ker_comp` | `ker (g.comp f) = (ker g).comap f` | none |
| `ker_prod` | `ker (prod f g) = ker f ⊓ ker g` | none |
| `ker_inf` | `ker (f ⊓ g) = ker f ∩ ker g` | none |
