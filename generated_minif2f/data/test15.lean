import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.NormNum

theorem expression_equals_one :
  ((100 ^ 2 - 7 ^ 2):ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 :=
by
  have h1 : (100 ^ 2 - 7 ^ 2) = (100 - 7) * (100 + 7) := by ring
  have h2 : (70 ^ 2 - 11 ^ 2) = (70 - 11) * (70 + 11) := by ring
  rw [h1, h2]
  field_simp
  ring_nf
  norm_num