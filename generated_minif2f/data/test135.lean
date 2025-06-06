import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators
import Mathlib.Tactic

open BigOperators

lemma prod_range_7 : ∏ k in Finset.range 7, (2^(2^k) + 3^(2^k)) = 3^128 - 2^128 :=
by
  have h : ∏ k in Finset.range 7, (2^(2^k) + 3^(2^k)) = ∏ k in Finset.range 7, (3^(2^k) - 2^(2^k)) :=
    Finset.prod_congr rfl (λ k hk, by rw [add_comm, sub_eq_add_neg, neg_neg])
  rw [h]
  have h2 : ∏ k in Finset.range 7, (3^(2^k) - 2^(2^k)) = (3^128 - 2^128) :=
    by norm_num
  exact h2