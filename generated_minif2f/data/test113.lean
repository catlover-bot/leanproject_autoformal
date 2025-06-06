import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset
open BigOperators

lemma sum_logb_eq_21000 :
  (∑ k in (Icc 1 20), (Real.logb (5^k) (3^(k^2)))) * (∑ k in (Icc 1 100), (Real.logb (9^k) (25^k))) = 21000 :=
by
  have h1 : ∀ k ∈ Icc 1 20, Real.logb (5^k) (3^(k^2)) = k / (k^2) * Real.logb 5 3 := by
    intros k hk
    rw [Real.logb_pow, Real.logb_pow, mul_div_assoc, mul_comm]
    congr
    ring
  have h2 : ∑ k in Icc 1 20, Real.logb (5^k) (3^(k^2)) = ∑ k in Icc 1 20, k / (k^2) * Real.logb 5 3 := by
    apply sum_congr rfl h1
  have h3 : ∑ k in Icc 1 20, k / (k^2) = ∑ k in Icc 1 20, 1 / k := by
    apply sum_congr rfl
    intros k hk
    rw [div_eq_div_iff, mul_one]
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one (mem_Icc.1 hk).1))
  have h4 : ∑ k in Icc 1 20, 1 / k = 1 := by
    norm_num
  have h5 : ∑ k in Icc 1 20, Real.logb (5^k) (3^(k^2)) = Real.logb 5 3 := by
    rw [h2, h3, h4, one_mul]
  have h6 : ∀ k ∈ Icc 1 100, Real.logb (9^k) (25^k) = k * Real.logb 9 25 := by
    intros k hk
    rw [Real.logb_pow, Real.logb_pow, mul_comm]
  have h7 : ∑ k in Icc 1 100, Real.logb (9^k) (25^k) = ∑ k in Icc 1 100, k * Real.logb 9 25 := by
    apply sum_congr rfl h6
  have h8 : ∑ k in Icc 1 100, k = 5050 := by
    norm_num
  have h9 : ∑ k in Icc 1 100, Real.logb (9^k) (25^k) = 5050 * Real.logb 9 25 := by
    rw [h7, h8, mul_comm]
  have h10 : Real.logb 5 3 * (5050 * Real.logb 9 25) = 21000 := by
    norm_num
  rw [h5, h9, h10]