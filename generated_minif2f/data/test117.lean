import Mathlib.Data.Nat.Factorial
import Mathlib.Data.Real.Basic

open Nat

theorem exists_square_for_factorial_difference (n : ℕ) (h : 9 ≤ n) : 
  ∃ (x : ℕ), (x : ℝ)^2 = ((n + 2)! - (n + 1)!) / n! :=
begin
  have h1 : ((n + 2)! - (n + 1)!) / n! = (n + 1) * (n + 1),
  { rw [factorial_succ, factorial_succ, mul_sub, mul_assoc, mul_assoc, ←mul_sub],
    simp [factorial, mul_comm, mul_assoc] },
  use n + 1,
  rw [h1, Nat.cast_mul, Nat.cast_add, Nat.cast_one],
  ring,
end