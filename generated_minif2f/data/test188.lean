import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

theorem sum_Icc_mod_4 : (∑ k in Icc 1 12, k) % 4 = 2 := by
  have h_sum : ∑ k in Icc 1 12, k = 78 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
    norm_num
  rw [h_sum]
  norm_num