import data.real.basic
import data.finset
import algebra.big_operators

open_locale big_operators
open finset

theorem log_sum_product :
  (∑ k in (Icc 1 20), real.logb (5^k) (3^(k^2))) * (∑ k in (Icc 1 100), real.logb (9^k) (25^k)) = 21000 :=
begin
  have h1 : ∑ k in Icc 1 20, real.logb (5^k) (3^(k^2)) = ∑ k in Icc 1 20, k * real.logb 5 3,
  { apply sum_congr rfl,
    intros k hk,
    rw real.logb_pow,
    rw real.logb_pow,
    rw mul_comm,
    rw mul_div_cancel_left,
    exact ne_of_gt (real.logb_pos (by norm_num) (by norm_num)) },
  
  have h2 : ∑ k in Icc 1 100, real.logb (9^k) (25^k) = ∑ k in Icc 1 100, k * real.logb 9 25,
  { apply sum_congr rfl,
    intros k hk,
    rw real.logb_pow,
    rw real.logb_pow,
    rw mul_comm,
    rw mul_div_cancel_left,
    exact ne_of_gt (real.logb_pos (by norm_num) (by norm_num)) },

  rw [h1, h2],
  rw [sum_mul, sum_mul],
  have h3 : ∑ k in Icc 1 20, k = 20 * 21 / 2,
  { rw sum_range_id,
    norm_num },
  have h4 : ∑ k in Icc 1 100, k = 100 * 101 / 2,
  { rw sum_range_id,
    norm_num },
  
  rw [h3, h4],
  field_simp,
  norm_num,
  rw [mul_assoc, mul_assoc, mul_comm (real.logb 5 3), ←mul_assoc, ←mul_assoc],
  have h5 : real.logb 5 3 * real.logb 9 25 = 1,
  { rw [real.logb_div_logb, real.logb_div_logb],
    norm_num },
  rw h5,
  norm_num,
end