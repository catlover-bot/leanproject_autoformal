import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

theorem mathd_numbertheory_353
  (s : ℕ)
  (h₀ : s = ∑ k in Icc 2010 4018, k) :
  s % 2009 = 0 :=
by
  have h₁ : ∑ k in Icc 2010 4018, k = (4018 * 4019) / 2 - (2009 * 2010) / 2 :=
    by rw [sum_Icc_eq_sub_sum_Icc, sum_range_id, sum_range_id]
  rw [h₀, h₁]
  have h₂ : (4018 * 4019) / 2 - (2009 * 2010) / 2 = 2009 * 1005 :=
    by norm_num
  rw [h₂]
  exact Nat.mod_mul_left_div_self 2009 1005