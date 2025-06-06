import Mathlib.Data.Real.Basic

theorem abs_sum_eq_x_plus_2_imp_x_in_0_1 (x : ℝ) :
  abs (x - 1) + abs x + abs (x + 1) = x + 2 → 0 ≤ x ∧ x ≤ 1 :=
begin
  intro h,
  by_cases h1 : x < -1,
  { have : abs (x - 1) = -(x - 1) ∧ abs x = -x ∧ abs (x + 1) = -(x + 1),
    { split; [apply abs_of_neg, apply abs_of_neg, apply abs_of_neg];
      linarith },
    rw [this.1, this.2.1, this.2.2] at h,
    linarith },
  by_cases h2 : x ≥ 1,
  { have : abs (x - 1) = x - 1 ∧ abs x = x ∧ abs (x + 1) = x + 1,
    { split; [apply abs_of_nonneg, apply abs_of_nonneg, apply abs_of_nonneg];
      linarith },
    rw [this.1, this.2.1, this.2.2] at h,
    linarith },
  have h3 : -1 ≤ x ∧ x < 1,
  { split; linarith },
  by_cases h4 : x < 0,
  { have : abs (x - 1) = 1 - x ∧ abs x = -x ∧ abs (x + 1) = x + 1,
    { split; [apply abs_of_nonpos, apply abs_of_neg, apply abs_of_nonneg];
      linarith },
    rw [this.1, this.2.1, this.2.2] at h,
    linarith },
  have h5 : 0 ≤ x ∧ x < 1,
  { split; linarith },
  have : abs (x - 1) = 1 - x ∧ abs x = x ∧ abs (x + 1) = x + 1,
  { split; [apply abs_of_nonpos, apply abs_of_nonneg, apply abs_of_nonneg];
    linarith },
  rw [this.1, this.2.1, this.2.2] at h,
  linarith,
end