import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Int.Basic

open Int

theorem abs_calculation : abs (((3491 - 60) * (3491 + 60) - 3491^2) : ℤ) = 3600 := by
  norm_num