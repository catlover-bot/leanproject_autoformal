import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Nat

theorem f_divides_f {m n : ℕ} (f : ℕ → ℕ) (h₀ : ∀ x, f x = 4^x + 6^x + 9^x) (h₁ : 0 < m ∧ 0 < n) (h₂ : m ≤ n) : f (2^m) ∣ f (2^n) :=
begin
  have h₃ : 2^m ≤ 2^n := pow_le_pow_of_le_left (by norm_num) h₂,
  rw [h₀, h₀],
  apply dvd_add,
  { apply dvd_add,
    { apply pow_dvd_pow, exact h₃ },
    { apply pow_dvd_pow, exact h₃ } },
  { apply pow_dvd_pow, exact h₃ }
end