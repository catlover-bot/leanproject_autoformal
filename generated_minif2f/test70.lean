import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma nat_divisibility (n : ℕ) (h₁ : n ≤ 9) (h₂ : 11 ∣ (20 * 100 + 10 * n + 7)) : n = 5 := by
  have h₃ : 11 ∣ (2000 + 10 * n + 7) := h₂
  have h₄ : 11 ∣ (2007 + 10 * n) := by
    rw [←Nat.add_assoc, Nat.add_comm 2000 7]
    exact h₃
  have h₅ : 11 ∣ (10 * n + 2007) := by
    rw [Nat.add_comm]
    exact h₄
  have h₆ : 2007 % 11 = 5 := by norm_num
  have h₇ : (10 * n + 2007) % 11 = 0 := Nat.dvd_iff_mod_eq_zero.mp h₅
  have h₈ : (10 * n + 5) % 11 = 0 := by
    rw [←Nat.add_mod, h₆]
    exact h₇
  have h₉ : 10 * n % 11 = 6 := by
    rw [Nat.add_mod_eq_iff_eq_sub_mod, h₈]
    norm_num
  have h₁₀ : 10 * n ≡ 6 [MOD 11] := Nat.modeq_iff_dvd.mp h₉
  have h₁₁ : 10 ≡ 10 [MOD 11] := Nat.modeq.refl 10
  have h₁₂ : n ≡ 6 * 10⁻¹ [MOD 11] := Nat.modeq.mul_right_cancel' 10 h₁₀ h₁₁
  have h₁₃ : 10⁻¹ ≡ 10 [MOD 11] := by norm_num
  have h₁₄ : n ≡ 6 * 10 [MOD 11] := h₁₂.trans (Nat.modeq.mul_right 6 h₁₃)
  have h₁₅ : n ≡ 5 [MOD 11] := by norm_num at h₁₄; exact h₁₄
  have h₁₆ : n = 5 := by
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h₁ (λ h, by rw [h] at h₁₅; norm_num at h₁₅))
    · exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Nat.lt_succ_self 5)) (λ h, by rw [h] at h₁₅; norm_num at h₁₅))
  exact h₁₆