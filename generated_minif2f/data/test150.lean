import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

open Real

lemma pow_one_div_lt_two_sub_one_div (n : ℕ) (hn : n ≠ 0) :
  (n:ℝ)^((1:ℝ) / n) < 2 - 1 / n :=
begin
  have n_pos : (n:ℝ) > 0 := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn),
  have h1 : (1:ℝ) / n > 0 := div_pos zero_lt_one n_pos,
  have h2 : (n:ℝ)^((1:ℝ) / n) < exp (1 / n * log n),
  { rw [exp_log n_pos],
    exact rpow_lt_rpow_of_exponent_lt n_pos h1 (by norm_num) },
  have h3 : exp (1 / n * log n) < 2 - 1 / n,
  { have : 1 / n * log n < log 2 - 1 / n,
    { rw [sub_eq_add_neg, ← log_inv, ← log_mul (exp_pos (1 / n * log n)) (exp_pos (1 / n))],
      apply log_lt_log,
      { apply mul_pos,
        { exact exp_pos (1 / n * log n) },
        { exact exp_pos (1 / n) } },
      { apply mul_pos,
        { exact exp_pos (1 / n) },
        { exact exp_pos (1 / n) } },
      rw [← exp_add, add_comm, ← sub_eq_add_neg],
      apply exp_lt_exp,
      linarith [log_pos (by norm_num : (2:ℝ) > 1)] },
    exact lt_of_lt_of_le this (le_of_eq (sub_add_cancel _ _)) },
  exact lt_trans h2 h3,
end