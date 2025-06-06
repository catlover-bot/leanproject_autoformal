import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

lemma nat_divisibility (n : ℕ) (h₁ : n ≤ 9) (h₂ : 18 ∣ (374 * 10 + n)) : n = 4 := by
  have h₃ : 374 * 10 + n = 3740 + n := by ring
  have h₄ : 18 ∣ 3740 + n := by rwa [h₃]
  have h₅ : 3740 % 18 = 8 := by norm_num
  have h₆ : (3740 + n) % 18 = (8 + n) % 18 := by rw [Nat.add_mod, h₅]
  have h₇ : (8 + n) % 18 = 0 := by
    rw [←Nat.dvd_iff_mod_eq_zero] at h₄
    exact h₄
  have h₈ : 8 + n = 18 := by
    linarith [Nat.mod_eq_zero_of_dvd h₇]
  linarith