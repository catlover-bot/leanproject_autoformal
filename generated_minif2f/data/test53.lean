import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem negative_integer_bound (x : ℤ) (h₀ : x < 0) (h₁ : (24 * x) % 1199 = 15) : x ≤ -449 := 
  by
  have h₂ : 24 * x ≡ 15 [ZMOD 1199] := Int.modeq_iff_dvd.2 (by rw [Int.sub_eq_add_neg, Int.add_comm, ←Int.mod_def, h₁]; exact dvd_refl _)
  obtain ⟨k, hk⟩ := h₂
  have : x = (1199 * k + 15) / 24 := by
    rw [hk, Int.add_comm, Int.mul_comm]
    exact Int.div_eq_of_eq_mul_right (by norm_num) rfl
  have h₃ : 24 * x < 0 := by linarith
  have h₄ : 1199 * k + 15 < 0 := by
    rw [←Int.mul_div_cancel' (by norm_num : 24 ≠ 0) this]
    exact h₃
  have h₅ : 1199 * k < -15 := by linarith
  have h₆ : k < -15 / 1199 := by
    apply Int.div_lt_of_lt_mul
    norm_num
    exact h₅
  have h₇ : k ≤ -1 := by linarith
  have h₈ : x ≤ -449 := by
    calc
      x = (1199 * k + 15) / 24 := this
      _ ≤ (1199 * -1 + 15) / 24 := by
        apply Int.div_le_div_of_le_of_pos
        linarith
        norm_num
      _ = -449 := by norm_num
  exact h₈