import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem irrational_function (f : ℚ → ℝ) 
  (h_mul : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y) 
  (h_prime : ∀ p, prime p → f p = p) : 
  f (25 /. 11) < 0 := 
begin
  have h_pos : (25 : ℚ) > 0 := by norm_num,
  have h_pos' : (11 : ℚ) > 0 := by norm_num,
  have h_f_25_11 : f (25 /. 11) = f 25 - f 11,
  { have h_mul' := h_mul 25 h_pos 11 h_pos',
    rw [Rat.mul_num_denom, Rat.mul_denom_denom] at h_mul',
    exact h_mul' },
  have h_f_25 : f 25 = f (5 * 5),
  { rw [←Rat.mul_num_denom, Rat.mul_denom_denom],
    exact h_mul 5 (by norm_num) 5 (by norm_num) },
  rw [h_f_25, h_mul 5 (by norm_num) 5 (by norm_num)] at h_f_25_11,
  have h_f_5 : f 5 = 5,
  { exact h_prime 5 (by norm_num) },
  rw [h_f_5, h_f_5] at h_f_25_11,
  have h_f_11 : f 11 = 11,
  { exact h_prime 11 (by norm_num) },
  rw [h_f_11] at h_f_25_11,
  linarith,
end