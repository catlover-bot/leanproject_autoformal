import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Nat
open Finset

theorem sum_of_prime_divisors_of_500 :
  ∀ (a : ℕ), a = (∑ k in (nat.divisors 500), k) → ∑ k in finset.filter (λ x, nat.prime x) (nat.divisors a), k = 25 :=
begin
  intro a,
  intro h,
  have h1 : nat.divisors 500 = {1, 2, 4, 5, 10, 20, 25, 50, 100, 125, 250, 500},
  { rw nat.divisors_eq_filter,
    simp [nat.mem_divisors, nat.dvd_iff_mod_eq_zero],
    norm_num },
  have h2 : ∑ k in {1, 2, 4, 5, 10, 20, 25, 50, 100, 125, 250, 500}, k = 1172,
  { norm_num },
  rw h1 at h,
  rw h2 at h,
  have h3 : a = 1172 := h,
  rw h3,
  have h4 : finset.filter (λ x, nat.prime x) (nat.divisors 1172) = {2, 5},
  { rw nat.divisors_eq_filter,
    simp [nat.mem_divisors, nat.dvd_iff_mod_eq_zero],
    norm_num,
    ext,
    simp [nat.prime_def_lt, nat.dvd_iff_mod_eq_zero],
    norm_num },
  rw h4,
  norm_num,
end