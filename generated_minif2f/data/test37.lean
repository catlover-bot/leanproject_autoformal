import Mathlib.Data.Nat.Factorial
import Mathlib.Tactic

open Nat

theorem factorial_lt_power (n : ℕ) (h : 3 ≤ n) : n! < n^(n - 1) :=
begin
  induction n using Nat.strong_induction_on with n ih,
  cases n,
  { norm_num at h },
  cases n,
  { norm_num at h },
  cases n,
  { norm_num at h },
  -- Base case: n = 3
  { norm_num },
  -- Inductive step: assume the statement holds for all m < n, prove for n
  { have h₁ : 3 ≤ n := Nat.le_of_succ_le_succ h,
    have ih' : ∀ m, 3 ≤ m → m < n → m! < m^(m - 1) := λ m hm hmn, ih m hmn hm,
    have : n! = n * (n - 1)! := by rw [factorial_succ, Nat.sub_add_cancel h₁],
    have : (n - 1)! < (n - 1)^(n - 2) := ih' (n - 1) (Nat.le_of_succ_le h) (Nat.pred_lt h₁),
    have : n * (n - 1)! < n * (n - 1)^(n - 2) := Nat.mul_lt_mul_of_pos_left this (Nat.zero_lt_succ _),
    have : n * (n - 1)^(n - 2) ≤ n^(n - 1),
    { apply Nat.pow_le_pow_of_le_left,
      exact Nat.le_of_succ_le h,
      exact Nat.pred_le _ },
    exact lt_of_lt_of_le this this }
end