import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Nat

theorem exists_square_eq_factorial_div (n : ℕ) (h : 9 ≤ n) : 
  ∃ (x : ℕ), (x : ℝ)^2 = ((n + 2)! - (n + 1)!) / n! := 
begin
  have h₁ : (n + 2)! = (n + 2) * (n + 1) * n!,
  { rw [factorial_succ, factorial_succ, mul_assoc] },
  have h₂ : (n + 1)! = (n + 1) * n!,
  { rw factorial_succ },
  rw [h₁, h₂],
  have h₃ : ((n + 2) * (n + 1) * n! - (n + 1) * n!) / n! = (n + 2) * (n + 1) - (n + 1),
  { rw [Nat.sub_mul, Nat.mul_div_cancel_left _ (factorial_pos n), Nat.mul_div_cancel_left _ (factorial_pos n)] },
  rw h₃,
  have h₄ : (n + 2) * (n + 1) - (n + 1) = (n + 1) * n,
  { ring },
  rw h₄,
  use (n + 1 : ℕ),
  norm_cast,
  ring,
end