import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem sequence_problem (x : ℝ) (n : ℕ) (a : ℕ → ℝ)
  (h : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1))
  (h1 : a 1 = 2 * x - 3)
  (h2 : a 2 = 5 * x - 11)
  (h3 : a 3 = 3 * x + 1)
  (h4 : a n = 2009) :
  n = 502 :=
begin
  have h_diff : ∀ m, a (m + 1) - a m = a 2 - a 1,
  { intro m,
    induction m with m ih,
    { ring },
    { rw [h, ih] } },
  have h_diff_1 : a 2 - a 1 = a 3 - a 2,
  { rw [h 1] },
  have h_diff_2 : a 2 - a 1 = (5 * x - 11) - (2 * x - 3),
  { rw [h1, h2], ring },
  have h_diff_3 : a 3 - a 2 = (3 * x + 1) - (5 * x - 11),
  { rw [h2, h3], ring },
  have h_eq : a 2 - a 1 = -2 * x + 8,
  { rw [h_diff_2], ring },
  have h_eq_2 : a 3 - a 2 = -2 * x + 12,
  { rw [h_diff_3], ring },
  have h_contradiction : -2 * x + 8 = -2 * x + 12,
  { rw [←h_diff_1, h_eq, h_eq_2] },
  linarith,
  have h_const : ∀ m, a m = a 1 + (m - 1) * (a 2 - a 1),
  { intro m,
    induction m with m ih,
    { rw [zero_sub, zero_mul, add_zero, h1] },
    { rw [succ_sub_succ, add_comm, ←add_assoc, ih, h_diff m] } },
  have h_a_n : a n = a 1 + (n - 1) * (a 2 - a 1),
  { apply h_const },
  rw [h_a_n, h4, h1, h_eq],
  linarith,
end