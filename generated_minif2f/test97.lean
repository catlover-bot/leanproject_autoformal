import Mathlib.Data.Nat.Basic

namespace Nat

theorem problem (a m c : ℕ) (h : a + m + c = 12) : a * m * c + a * m + m * c + a * c ≤ 112 := by
  have h₁ : a * m * c + a * m + m * c + a * c = (a + 1) * (m + 1) * (c + 1) - (a + m + c + 1) := by
    ring
  rw [h₁]
  have h₂ : (a + 1) * (m + 1) * (c + 1) ≤ 125 := by
    linarith [h]
  linarith [h, h₂]

end Nat