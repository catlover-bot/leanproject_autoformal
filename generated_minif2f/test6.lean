import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators
import Mathlib.Tactic

open BigOperators

theorem sum_of_squares_mod_10 : (∑ x in finset.range 10, ((x + 1)^2)) % 10 = 5 := by
  norm_num [finset.sum_range_succ, pow_succ, pow_two, add_assoc, add_comm, add_left_comm]