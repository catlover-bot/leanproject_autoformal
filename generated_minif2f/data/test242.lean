import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Real

theorem simplify_expression (x : ℝ) (hx : x ≠ 0) : 12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  field_simp [hx]
  ring_nf
  norm_num