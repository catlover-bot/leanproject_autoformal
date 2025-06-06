import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem unique_n (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ (123456 - n)) : n = 34 := by
  obtain ⟨k, hk⟩ := h₁
  have h₂ : n = 123456 - 101 * k := by
    rw [hk]
  have h₃ : 123456 - 101 * k < 101 := by
    rw [←h₂]
    exact h₀
  have h₄ : 123355 < 101 * k := by
    linarith
  have h₅ : 1221 < k := by
    norm_num at h₄
    exact Nat.div_lt_of_lt_mul h₄
  have h₆ : k ≤ 1222 := by
    have : 101 * 1222 = 123422 := by norm_num
    linarith
  have h₇ : k = 1222 := by
    linarith
  rw [h₇] at h₂
  norm_num at h₂
  exact h₂