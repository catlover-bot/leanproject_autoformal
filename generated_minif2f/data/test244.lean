import Mathlib.Data.Real.Basic

theorem mathd_algebra_338
(a b c : ℝ)
(h₀ : 3 * a + b + c = -3)
(h₁ : a + 3 * b + c = 9)
(h₂ : a + b + 3 * c = 19) :
a * b * c = -56 :=
by
  have ha : a = -4 := by
    linarith [h₀, h₁, h₂]
  have hb : b = 2 := by
    rw [ha] at h₀ h₁ h₂
    linarith [h₀, h₁]
  have hc : c = 7 := by
    rw [ha, hb] at h₀ h₁ h₂
    linarith [h₀]
  rw [ha, hb, hc]
  norm_num