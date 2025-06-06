import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators.Ring

open Finset

theorem sum_of_cubes (n : ℕ) : ∑ k in range n, k^3 = (∑ k in range n, k)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, pow_succ, ih]
    ring