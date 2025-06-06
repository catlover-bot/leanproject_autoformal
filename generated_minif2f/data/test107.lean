import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem sqrt_inequality (x : ℝ) (h1 : 0 ≤ 3 - x) (h2 : 0 ≤ x + 1) (h3 : 1 / 2 < sqrt (3 - x) - sqrt (x + 1)) :
  -1 ≤ x ∧ x < 1 - sqrt 31 / 8 :=
begin
  -- Establish domain constraints
  have h4 : x ≤ 3, from le_of_sub_nonneg h1,
  have h5 : -1 ≤ x, from le_of_sub_nonneg h2,

  -- Analyze the inequality
  have h6 : 1 / 2 < sqrt (3 - x) - sqrt (x + 1), from h3,
  have h7 : (1 / 2)^2 < (sqrt (3 - x) - sqrt (x + 1))^2, from pow_lt_pow_of_lt_left h6 (by norm_num) (by norm_num),
  rw [pow_two, pow_two, sub_sq] at h7,
  have h8 : 1 / 4 < (3 - x) + (x + 1) - 2 * sqrt ((3 - x) * (x + 1)), from h7,
  linarith only [h8],

  -- Simplify and solve
  have h9 : 1 / 4 < 4 - 2 * sqrt ((3 - x) * (x + 1)), by linarith,
  have h10 : 2 * sqrt ((3 - x) * (x + 1)) < 15 / 8, by linarith,
  have h11 : sqrt ((3 - x) * (x + 1)) < 15 / 16, from (lt_div_iff (by norm_num : (0 : ℝ) < 2)).mp h10,
  have h12 : ((3 - x) * (x + 1)) < (15 / 16)^2, from pow_lt_pow_of_lt_left h11 (by norm_num) (by norm_num),
  rw [pow_two] at h12,
  have h13 : (3 - x) * (x + 1) < 225 / 256, from h12,

  -- Solve quadratic inequality
  have h14 : 3 * x + 3 < 225 / 64, by linarith only [h13],
  have h15 : x < 1 - sqrt 31 / 8, by linarith,

  -- Combine results
  exact ⟨h5, h15⟩,
end