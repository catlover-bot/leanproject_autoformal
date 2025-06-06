import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AMC12B2002P7

theorem amc12b_2002_p7
  (a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : b = a + 1)
  (h₂ : c = b + 1)
  (h₃ : a * b * c = 8 * (a + b + c)) :
  a^2 + (b^2 + c^2) = 77 := 
by
  obtain ⟨ha, hb, hc⟩ := h₀
  rw [h₁, h₂] at h₃
  have h₄ : c = a + 2 := by linarith
  rw [h₁, h₄] at h₃
  have h₅ : a * (a + 1) * (a + 2) = 8 * (3 * a + 3) := by linarith
  have h₆ : a * (a + 1) * (a + 2) = 24 * a + 24 := by ring
  rw [h₆] at h₅
  have h₇ : a * (a + 1) * (a + 2) = 24 * a + 24 := by linarith
  have h₈ : a = 2 := by linarith
  rw [h₈, h₁, h₄]
  norm_num

end AMC12B2002P7