import Mathlib.Data.Real.Basic

open Real

theorem division_identity (x : ℝ) (hx : x ≠ 0) : 12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  field_simp [hx]
  ring_nf
  norm_num