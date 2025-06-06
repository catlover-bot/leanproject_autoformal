import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Solution

theorem find_n (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ (123456 - n)) : n = 34 := by
  have h₂ : 123456 % 101 = 34 := by norm_num
  have h₃ : (123456 - n) % 101 = 0 := Nat.dvd_iff_mod_eq_zero.mp h₁
  have h₄ : 123456 % 101 = n % 101 := by
    rw [←Nat.sub_mod, h₃, Nat.zero_mod]
  rw [h₂] at h₄
  have h₅ : n % 101 = 34 := h₄
  have h₆ : n = 34 := Nat.mod_eq_of_lt h₀ ▸ h₅
  exact h₆

end Solution