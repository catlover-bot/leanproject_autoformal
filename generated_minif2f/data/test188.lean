import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators
import Mathlib.Tactic.NormNum

open Finset

lemma sum_Icc_mod_4 : (∑ k in Icc 1 12, k) % 4 = 2 := by
  norm_num