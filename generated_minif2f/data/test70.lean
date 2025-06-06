import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem nat_divisibility (n : ℕ) (h₁ : n ≤ 9) (h₂ : 11 ∣ (20 * 100 + 10 * n + 7)) : n = 5 := 
  by
  have h₃ : 20 * 100 + 10 * n + 7 = 2007 + 10 * n := by norm_num
  rw [h₃] at h₂
  have h₄ : 2007 % 11 = 5 := by norm_num
  have h₅ : 11 ∣ 2007 + 10 * n ↔ 11 ∣ 10 * n + 5 := by
    rw [← Nat.dvd_add_iff_right (dvd_refl 2007)]
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero] at h₂
    rw [Nat.add_mod, h₄, add_comm, Nat.add_mod, Nat.mod_self, zero_add] at h₂
    exact ⟨λ h, h, λ h, h⟩
  rw [h₅] at h₂
  have h₆ : 10 * n % 11 = 6 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h₂
    rw [Nat.add_mod, h₂, Nat.mod_self, zero_add]
  have h₇ : 10 * n ≡ 6 [MOD 11] := by
    rw [Nat.modeq_iff_dvd, Nat.dvd_iff_mod_eq_zero]
    exact h₆
  have h₈ : 10 * 5 % 11 = 6 := by norm_num
  have h₉ : 10 * n ≡ 10 * 5 [MOD 11] := by
    rw [Nat.modeq_iff_dvd, Nat.dvd_iff_mod_eq_zero]
    rw [Nat.mul_mod, h₈, Nat.mul_mod, h₆]
  have h₁₀ : n ≡ 5 [MOD 11] := Nat.modeq_of_mul_left 10 (Nat.succ_pos 10) h₉
  have h₁₁ : n = 5 := by
    linarith [h₁₀.symm, h₁]
  exact h₁₁