import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma divisible_by_9 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) : ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := by
  have h₂ : 3 ∣ (n + 4) + (n + 6) + (n + 8) := by
    apply Nat.dvd_add
    apply Nat.dvd_add
    · exact h₁
    · exact h₁
    · exact h₁
  have h₃ : ((n + 4) + (n + 6) + (n + 8)) % 3 = 0 := by
    exact Nat.dvd_iff_mod_eq_zero.mp h₂
  have h₄ : ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 := by
    calc
      ((n + 4) + (n + 6) + (n + 8)) % 9
          = (3 * n + 18) % 9 := by ring
      _ = (3 * n % 9 + 18 % 9) % 9 := Nat.add_mod _ _ _
      _ = (0 + 0) % 9 := by
        rw [Nat.mul_mod, h₁, Nat.zero_mod, Nat.mod_self]
      _ = 0 := Nat.zero_mod _
  exact h₄

theorem main_theorem : ∀ (n : ℕ), 0 < n → 3 ∣ n → ((n + 4) + (n + 6) + (n + 8)) % 9 = 0 :=
  divisible_by_9