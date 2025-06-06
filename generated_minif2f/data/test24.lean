import Mathlib.Data.Real.Basic

theorem real_numbers_proof (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) 
  (h₁ : 9 * b = 20 * c) (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c :=
begin
  have hb : b = (20 / 9) * c,
  { rw [← h₁, mul_div_cancel_left _ (by norm_num : (9 : ℝ) ≠ 0)] },
  have ha : a = (4 / 7) * b,
  { rw [← h₂, mul_div_cancel_left _ (by norm_num : (7 : ℝ) ≠ 0)] },
  rw [ha, hb],
  calc
    63 * ((4 / 7) * ((20 / 9) * c))
        = 63 * ((80 / 63) * c) : by ring
    ... = 80 * c : by ring,
end