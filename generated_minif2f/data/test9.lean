import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem nat_divisibility (n : ℕ) (h₁ : n ≤ 9) (h₂ : 18 ∣ (374 * 10 + n)) : n = 4 := 
by
  have h₃ : 3740 % 18 = 14 := by norm_num
  have h₄ : (3740 + n) % 18 = 0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp h₂
  have h₅ : (14 + n) % 18 = 0 := by
    rw [←Nat.add_mod, h₃]
    exact h₄
  have h₆ : 14 + n = 18 := by
    linarith [Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mod_eq_zero h₅)]
  linarith