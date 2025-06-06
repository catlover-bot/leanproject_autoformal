import Mathlib.Data.Real.Basic

theorem problem_statement :
  ∀ (a b c : ℝ), (0 < a ∧ 0 < b ∧ 0 < c) → (9 * b = 20 * c) → (7 * a = 4 * b) → (63 * a = 80 * c) :=
begin
  intros a b c hpos h1 h2,
  have h3 : 63 * a = 9 * (7 * a), by ring,
  rw [h2] at h3,
  have h4 : 9 * (4 * b) = 36 * b, by ring,
  rw [h4] at h3,
  rw [h1] at h3,
  have h5 : 36 * b = 36 * (20 / 9 * c), by rw [←h1, mul_div_cancel' _ (ne_of_gt hpos.2.2)],
  rw [h5] at h3,
  have h6 : 36 * (20 / 9 * c) = 80 * c, by ring,
  rw [h6] at h3,
  exact h3,
end