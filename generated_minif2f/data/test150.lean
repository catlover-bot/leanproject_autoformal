import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow

open Real

theorem pow_one_div_lt_two_sub_one_div (n : ℕ) (hn : 1 ≤ n) :
  (n:ℝ)^((1:ℝ) / n) < 2 - 1 / n :=
begin
  have n_pos : 0 < (n : ℝ) := by exact_mod_cast nat.pos_of_ne_zero (ne_of_gt hn),
  have n_ge_one : (n : ℝ) ≥ 1 := by exact_mod_cast hn,
  let f : ℝ → ℝ := λ x, x^(1/x),
  have f_lim : tendsto f at_top (nhds 1),
  { apply tendsto.comp,
    { apply tendsto_exp_at_top.comp,
      apply tendsto_mul_at_top (tendsto_log_at_top.comp tendsto_id) tendsto_inv_at_top_zero },
    { apply tendsto_id } },
  have f_decreasing : ∀ x ≥ 1, ∀ y > x, f y < f x,
  { intros x hx y hy hxy,
    have : 0 < 1 / x - 1 / y := sub_pos_of_lt (one_div_lt_one_div_of_lt hxy (lt_of_lt_of_le zero_lt_one hx)),
    have : f y < f x ↔ y^(1/y) < x^(1/x) := iff.rfl,
    rw [← exp_lt_exp, exp_log (pow_pos (lt_of_lt_of_le zero_lt_one hx) (1/x)), exp_log (pow_pos (lt_of_lt_of_le zero_lt_one (le_of_lt hy)) (1/y))],
    apply exp_lt_exp.mpr,
    rw [log_rpow (lt_of_lt_of_le zero_lt_one (le_of_lt hy)), log_rpow (lt_of_lt_of_le zero_lt_one hx)],
    exact mul_lt_mul_of_pos_right (log_lt_log_of_lt hxy) (sub_pos_of_lt (one_div_lt_one_div_of_lt hxy (lt_of_lt_of_le zero_lt_one hx))) },
  have f_lt_two : ∀ x ≥ 1, f x < 2,
  { intros x hx,
    have : f x ≤ 1 + 1 / x,
    { rw [← exp_le_exp, exp_log (pow_pos (lt_of_lt_of_le zero_lt_one hx) (1/x))],
      apply exp_le_exp.mpr,
      rw [log_rpow (lt_of_lt_of_le zero_lt_one hx)],
      apply mul_le_mul_of_nonneg_right,
      { apply log_le_sub_one_of_pos,
        exact lt_of_lt_of_le zero_lt_one hx },
      { exact one_div_nonneg.mpr (le_of_lt (lt_of_lt_of_le zero_lt_one hx)) } },
    linarith },
  have : f n < 2 - 1 / n,
  { apply lt_of_le_of_lt (f_lt_two n n_ge_one),
    linarith },
  exact this,
end