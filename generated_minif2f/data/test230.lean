import Mathlib.Data.Real.Basic

open Real

theorem abs_inequality (x p : ℝ) (f : ℝ → ℝ) :
  (0 < p ∧ p < 15) →
  (p ≤ x ∧ x ≤ 15) →
  (f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) →
  15 ≤ f x :=
begin
  intros hp hx hf,
  have h1 : abs (x - p) + abs (x - 15) + abs (x - p - 15) ≥ 15,
  { cases le_or_lt x p with hxp hxp,
    { rw [abs_of_nonpos (sub_nonpos_of_le hxp), abs_of_nonneg (sub_nonneg_of_le hx.2)],
      rw [abs_of_nonpos (sub_nonpos_of_le (by linarith))],
      linarith },
    { cases le_or_lt x 15 with hx15 hx15,
      { rw [abs_of_nonneg (sub_nonneg_of_le (le_of_lt hxp)), abs_of_nonneg (sub_nonneg_of_le hx15)],
        rw [abs_of_nonpos (sub_nonpos_of_le (by linarith))],
        linarith },
      { rw [abs_of_nonneg (sub_nonneg_of_le (le_of_lt hxp)), abs_of_pos (sub_pos_of_lt hx15)],
        rw [abs_of_pos (sub_pos_of_lt (by linarith))],
        linarith } } },
  rw hf,
  exact h1,
end