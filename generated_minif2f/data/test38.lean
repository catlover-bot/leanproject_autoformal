import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem sqrt_sub_cubed_eq : sqrt 1000000 - 1000000^((1:ℝ)/3) = 900 :=
by
  have h1 : sqrt 1000000 = 1000 := by norm_num
  have h2 : 1000000^((1:ℝ)/3) = 100 := by norm_num
  rw [h1, h2]
  norm_num