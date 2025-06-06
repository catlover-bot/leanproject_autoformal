import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem mod_equation_solution (n : ℕ) : (2 * n) % 47 = 15 → n % 47 = 31 := by
  intro h₀
  have h₁ : 2 * n ≡ 15 [MOD 47] := Nat.ModEq.of_eq h₀
  have h₂ : 2 * 24 ≡ 1 [MOD 47] := by norm_num
  have h₃ : n ≡ 15 * 24 [MOD 47] := h₁.mul_right 24
  calc
    n % 47 = (15 * 24) % 47 := by
      apply Nat.ModEq.symm
      exact h₃
    _ = 31 := by norm_num