import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem power_mean_inequality (a b : ℝ) (n : ℕ) (h₁ : 0 < a ∧ 0 < b) (h₂ : 0 < n) : 
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h₃ : 0 < (a + b) / 2 := by
    linarith
  have h₄ : 0 < a^n ∧ 0 < b^n := by
    split
    · apply pow_pos h₁.1 h₂
    · apply pow_pos h₁.2 h₂
  have h₅ : 0 < (a^n + b^n) / 2 := by
    linarith
  apply pow_le_pow_of_le_left h₃ h₅
  apply le_of_pow_le_pow n h₅
  linarith
  ring
  linarith