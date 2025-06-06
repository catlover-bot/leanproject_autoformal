import Mathlib.Data.Real.Basic

open Real

theorem problem_statement :
  ∀ (x y : ℝ) (f g : ℝ → ℝ),
    (∀ t, f t = t^4) →
    (∀ t, g t = 5 * t^2 - 6) →
    f x = g x →
    f y = g y →
    x^2 < y^2 →
    y^2 - x^2 = 1 :=
begin
  intros x y f g hf hg hfx hfy hxy,
  rw [hf, hg] at hfx hfy,
  have hx : x^4 = 5 * x^2 - 6 := hfx,
  have hy : y^4 = 5 * y^2 - 6 := hfy,
  have h : y^4 - x^4 = (y^2 - x^2) * (y^2 + x^2),
  { ring },
  rw [hx, hy] at h,
  have : (5 * y^2 - 6) - (5 * x^2 - 6) = 5 * (y^2 - x^2),
  { ring },
  rw this at h,
  have : 5 * (y^2 - x^2) = (y^2 - x^2) * (y^2 + x^2),
  { linarith },
  have hneq : y^2 + x^2 ≠ 0,
  { linarith },
  have hdiv : 5 = y^2 + x^2,
  { exact (eq_div_iff hneq).mp this },
  linarith,
end