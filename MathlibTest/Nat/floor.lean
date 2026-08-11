import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.NormNum

/-!
Regression test for the Zulip thread about `Nat.floor_add_natCast` not applying after
`norm_num` normalises a numeric literal to an `OfNat` (rather than a `Nat.cast`).

`Nat.floor_add_ofNat` fires on the `OfNat` form produced by `norm_num`, so the proof
no longer needs the manual `(2 : ℝ) = ((2 : ℕ) : ℝ)` rewrite.
-/

example (a : ℝ) (ha : 0 ≤ a) : ⌊a + (30 / 15)⌋₊ = ⌊a⌋₊ + 2 := by
  norm_num
  rw [Nat.floor_add_ofNat ha]
