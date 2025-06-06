import Mathlib.Data.Real.Basic

open Real

theorem polynomial_evaluation (a b : ℝ) (f : ℝ → ℝ) :
  (∀ x, f x = a * x^4 - b * x^2 + x + 5) → (f (-3) = 2) → (f 3 = 8) :=
begin
  intros hf hfm3,
  have hfm3_exp : f (-3) = a * (-3)^4 - b * (-3)^2 + (-3) + 5,
  { rw hf, },
  have hfm3_simp : a * 81 - b * 9 - 3 + 5 = 2,
  { rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, mul_one, mul_one, mul_one, mul_one] at hfm3_exp,
    norm_num at hfm3_exp,
    exact hfm3_exp, },
  have hfm3_eq : a * 81 - b * 9 = 0,
  { linarith, },
  have hf3_exp : f 3 = a * 3^4 - b * 3^2 + 3 + 5,
  { rw hf, },
  have hf3_simp : a * 81 - b * 9 + 3 + 5 = 8,
  { rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, mul_one, mul_one, mul_one, mul_one] at hf3_exp,
    norm_num at hf3_exp,
    exact hf3_exp, },
  rw hfm3_eq at hf3_simp,
  norm_num at hf3_simp,
  exact hf3_simp,
end