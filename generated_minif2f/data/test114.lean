import data.real.basic
import data.finset
import analysis.special_functions.integrals
import analysis.special_functions.sqrt

open_locale big_operators
open finset real

theorem sum_reciprocal_sqrt_lt_198 : 
  ∑ k in (finset.Icc (2 : ℕ) 10000), (1 / real.sqrt k) < 198 :=
begin
  -- Use the integral approximation for the sum
  have integral_approx : ∫ x in (2 : ℝ)..10001, 1 / real.sqrt x = 2 * real.sqrt 10001 - 2 * real.sqrt 2,
  { rw [integral_deriv_eq_sub' (λ x, 2 * real.sqrt x) _ _],
    { simp [mul_div_cancel_left, ne_of_gt (sqrt_pos.2 zero_lt_two)] },
    { intros x hx, apply continuous_on_const.mul, exact continuous_on_sqrt.mono hx },
    { intros x hx, apply differentiable_at_const.mul, exact differentiable_at_sqrt (ne_of_gt hx) } },
  
  -- Calculate the value of the integral
  have integral_value : 2 * real.sqrt 10001 - 2 * real.sqrt 2 < 198,
  { norm_num,
    rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add'],
    norm_num,
    apply sqrt_lt_sqrt,
    norm_num,
    linarith },
  
  -- Use the integral to bound the sum
  apply lt_of_le_of_lt (sum_Icc_le_integral_of_continuous_on (λ x, 1 / real.sqrt x) _ _ _ _),
  { intros x hx, apply continuous_on_const.div, exact continuous_on_sqrt.mono hx },
  { intros x hx, apply div_nonneg, norm_num, apply sqrt_nonneg },
  { exact integral_value }
end