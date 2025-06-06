import Mathlib.Data.Real.Basic

theorem real_numbers_sum (m b : ℝ) : (m * 7 + b = -1) ∧ (m * (-1) + b = 7) → m + b = 5 :=
begin
  intro h,
  cases h with h1 h2,
  have h3 : 8 * m = -8,
  { linarith },
  have hm : m = -1,
  { linarith },
  have hb : b = 6,
  { linarith },
  linarith,
end