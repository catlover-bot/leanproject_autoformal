import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset

open Finset

theorem arithmetic_sequence_sum (a d : ℝ) :
  (∑ k in range 5, (a + k * d) = 70) →
  (∑ k in range 10, (a + k * d) = 210) →
  a = 42 / 5 :=
begin
  intros h1 h2,
  have h_sum5 : ∑ k in range 5, (a + k * d) = 5 * a + 10 * d,
  { rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_zero,
    ring },
  have h_sum10 : ∑ k in range 10, (a + k * d) = 10 * a + 45 * d,
  { rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_succ,
    rw sum_range_zero,
    ring },
  rw h_sum5 at h1,
  rw h_sum10 at h2,
  linarith,
end