import Mathlib.Data.Real.Basic

open Real

theorem abs_sum_normalized_inequality (a b : ℝ) :
  abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) :=
begin
  -- Multiply both sides by the common denominator
  let d := (1 + abs (a + b)) * (1 + abs a) * (1 + abs b),
  have h₁ : d > 0 := mul_pos (mul_pos (by linarith [abs_nonneg (a + b)]) (by linarith [abs_nonneg a])) (by linarith [abs_nonneg b]),
  apply (div_le_div_iff h₁ (by linarith [abs_nonneg (a + b)])).mpr,
  -- Clear denominators
  calc
    abs (a + b) * (1 + abs a) * (1 + abs b)
        ≤ (abs a + abs b) * (1 + abs a) * (1 + abs b) : by {
          apply mul_le_mul_of_nonneg_right,
          { apply mul_le_mul_of_nonneg_right,
            { exact abs_add a b, },
            { linarith [abs_nonneg b], }, },
          { linarith [abs_nonneg a], }, }
    ... = abs a * (1 + abs a) * (1 + abs b) + abs b * (1 + abs a) * (1 + abs b) : by ring
    ... ≤ abs a * (1 + abs a) * (1 + abs b) + abs b * (1 + abs b) * (1 + abs a) : by ring,
end