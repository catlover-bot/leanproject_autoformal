import Mathlib.Data.Finset
import Mathlib.Data.Nat.Factorial
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.NormNum

open Finset

lemma prod_odd_range : 
  finset.prod (finset.filter (λ x, ¬ even x) (finset.range 10000)) (id : ℕ → ℕ) = (10000!) / ((2^5000) * 5000!) :=
begin
  have h1 : (finset.filter (λ x, ¬ even x) (finset.range 10000)).card = 5000,
  { rw [card_filter, card_range, Nat.card_eq_of_bijective],
    { exact Nat.bijective_odd_iff.2 (by norm_num) },
    { exact Nat.bijective_odd_iff.1 (by norm_num) } },
  have h2 : (finset.filter (λ x, even x) (finset.range 10000)).card = 5000,
  { rw [card_filter, card_range, Nat.card_eq_of_bijective],
    { exact Nat.bijective_even_iff.2 (by norm_num) },
    { exact Nat.bijective_even_iff.1 (by norm_num) } },
  have h3 : (finset.range 10000).card = 10000 := card_range 10000,
  have h4 : (finset.prod (finset.range 10000) (id : ℕ → ℕ)) = 10000!,
  { rw prod_range_id },
  have h5 : (finset.prod (finset.filter (λ x, even x) (finset.range 10000)) (id : ℕ → ℕ)) = 2^5000 * 5000!,
  { rw [prod_filter, prod_range_id, Nat.factorial_eq_prod_range, Nat.factorial_eq_prod_range],
    norm_num },
  rw [←h4, ←h5, ←mul_div_assoc, mul_comm, mul_div_cancel],
  { exact prod_filter_mul_prod_filter_not (λ x, even x) (finset.range 10000) },
  { exact pow_ne_zero 5000 (by norm_num) }
end