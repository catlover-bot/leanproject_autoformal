import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime

open Nat

theorem factorial_divisible_by_80325 (n : ℕ) (h₀ : 0 < n) (h₁ : 80325 ∣ n!) : 17 ≤ n :=
begin
  have h80325 : 80325 = 3^2 * 5^2 * 7 * 17 := by norm_num,
  rw h80325 at h₁,
  have h3 : 3^2 ∣ n! := dvd_trans (dvd_mul_right (3^2) _) h₁,
  have h5 : 5^2 ∣ n! := dvd_trans (dvd_mul_right (5^2) _) h₁,
  have h7 : 7 ∣ n! := dvd_trans (dvd_mul_right 7 _) h₁,
  have h17 : 17 ∣ n! := dvd_trans (dvd_mul_right 17 _) h₁,
  have : 6 ≤ n := le_of_dvd (factorial_pos n) h3,
  have : 10 ≤ n := le_of_dvd (factorial_pos n) h5,
  have : 7 ≤ n := le_of_dvd (factorial_pos n) h7,
  have : 17 ≤ n := le_of_dvd (factorial_pos n) h17,
  exact this,
end