import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators
import Mathlib.Tactic.NormNum

open BigOperators

lemma prod_odd_mod_10 : (∏ k in finset.range 6, (2 * k + 1)) % 10 = 5 := by
  norm_num [finset.range, List.prod]