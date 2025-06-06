import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime

open Nat

theorem factorial_divisor_bound : ∀ (n : ℕ), 0 < n → 80325 ∣ n! → 17 ≤ n :=
begin
  intros n hn hdiv,
  have h80325 : 80325 = 3^2 * 5^2 * 7 * 17,
  { norm_num },
  rw h80325 at hdiv,
  have h3 : 3^2 ∣ n!,
  { apply dvd_trans _ hdiv, apply dvd_mul_right },
  have h5 : 5^2 ∣ n!,
  { apply dvd_trans _ hdiv, apply dvd_mul_right },
  have h7 : 7 ∣ n!,
  { apply dvd_trans _ hdiv, apply dvd_mul_right },
  have h17 : 17 ∣ n!,
  { apply dvd_trans _ hdiv, apply dvd_mul_right },
  have h3n : 3 ≤ n,
  { apply Nat.prime.dvd_factorial (prime_of_nat_prime 3) hn, exact h3 },
  have h5n : 5 ≤ n,
  { apply Nat.prime.dvd_factorial (prime_of_nat_prime 5) hn, exact h5 },
  have h7n : 7 ≤ n,
  { apply Nat.prime.dvd_factorial (prime_of_nat_prime 7) hn, exact h7 },
  have h17n : 17 ≤ n,
  { apply Nat.prime.dvd_factorial (prime_of_nat_prime 17) hn, exact h17 },
  exact h17n,
end