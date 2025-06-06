import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

lemma sum_of_cubes_eq_square_of_sum (n : ℕ) : ∑ k in range n, k^3 = (∑ k in range n, k)^2 :=
begin
  induction n with j ih,
  { -- Base case: n = 0
    simp, },
  { -- Inductive step: assume true for n = j, prove for n = j + 1
    rw [sum_range_succ, sum_range_succ, pow_succ, ih],
    ring, }
end