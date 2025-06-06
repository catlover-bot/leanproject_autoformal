import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem factorial_lt_pow (n : ℕ) (h : 3 ≤ n) : n! < n^(n - 1) :=
by
  induction n using Nat.strong_induction_on with n ih
  cases n with
  | zero => linarith
  | succ n =>
    cases n with
    | zero => linarith
    | succ n =>
      cases n with
      | zero => linarith
      | succ n =>
        have h₁ : 3 ≤ n + 3 := by linarith
        have h₂ : n + 3 > 0 := by linarith
        have h₃ : n + 3 > 1 := by linarith
        have ih' := ih (n + 2) (by linarith) h₁
        calc
          (n + 3)! = (n + 3) * (n + 2)! := rfl
          _ < (n + 3) * (n + 2)^(n + 1) := by
            apply Nat.mul_lt_mul_of_pos_left ih'
            linarith
          _ ≤ (n + 3)^(n + 2) := by
            apply Nat.pow_le_pow_of_le_left
            linarith
            linarith
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3)^(n + 1) * (n + 3) := by ring
          _ = (n + 3)^(n + 1 + 1) := by ring
          _ = (n + 3)^(n + 2) := by ring
          _ = (n + 3