import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators.Ring

open Finset

lemma sum_range_odd (n : ℕ) : ∑ k in range n, (2 * k + 1 : ℤ) = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp [mul_add, add_mul, add_assoc, add_comm, add_left_comm]

lemma sum_range_even (a n : ℕ) : ∑ k in range n, (a + 2 * k : ℤ) = n * a + n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp [mul_add, add_mul, add_assoc, add_comm, add_left_comm, Nat.succ_eq_add_one]
    ring

theorem main_theorem : ∀ (a : ℕ), even a → (↑∑ k in range 8, (2 * k + 1) - ↑∑ k in range 5, (a + 2 * k) = (4:ℤ)) → a = 8 := by
  intros a ha h
  have h1 : ∑ k in range 8, (2 * k + 1 : ℤ) = 64 := by
    rw [sum_range_odd]
    norm_num
  have h2 : ∑ k in range 5, (a + 2 * k : ℤ) = 5 * a + 10 := by
    rw [sum_range_even]
    norm_num
  rw [h1, h2] at h
  linarith