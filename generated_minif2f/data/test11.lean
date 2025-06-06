import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open BigOperators

lemma sum_range_100_mod_6 : (∑ k in (finset.range 101), k) % 6 = 4 :=
by
  have h : ∑ k in finset.range 101, k = 100 * 101 / 2 := finset.sum_range_id
  rw [h]
  norm_num
  exact Nat.mod_eq_of_lt (by norm_num)