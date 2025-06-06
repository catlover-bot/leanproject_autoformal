import data.nat.basic
import data.nat.prime
import data.finset
import data.nat.divisors

open finset

theorem mathd_numbertheory_451
(S : finset ℕ)
(h₀ : ∀ (n : ℕ), n ∈ S ↔ 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, ((nat.divisors m).card = 4 ∧ ∑ p in (nat.divisors m), p = n)) :
∑ k in S, k = 2016 :=
begin
  have h₁ : ∀ m, (nat.divisors m).card = 4 ↔ (∃ p, nat.prime p ∧ m = p^3) ∨ (∃ p q, nat.prime p ∧ nat.prime q ∧ p ≠ q ∧ m = p * q),
  { intro m,
    split,
    { intro h,
      rcases nat.four_divisors h with ⟨p, hp, rfl⟩ | ⟨p, q, hp, hq, hne, rfl⟩,
      { left, use [p, hp] },
      { right, use [p, q, hp, hq, hne] } },
    { rintro (⟨p, hp, rfl⟩ | ⟨p, q, hp, hq, hne, rfl⟩),
      { exact nat.four_divisors_of_prime_cube hp },
      { exact nat.four_divisors_of_two_distinct_primes hp hq hne } } },

  have h₂ : ∀ m, (nat.divisors m).card = 4 → ∑ p in (nat.divisors m), p = m + 1,
  { intros m h,
    rcases h₁ m with ⟨p, hp, rfl⟩ | ⟨p, q, hp, hq, hne, rfl⟩,
    { rw nat.divisors_prime_pow hp (by norm_num : 3 ≠ 0),
      simp [nat.divisors_prime_pow, hp, pow_succ, pow_zero, add_comm] },
    { rw nat.divisors_mul_of_prime hp hq hne,
      simp [nat.divisors_prime, hp, hq, add_comm] } },

  have h₃ : S = {2011, 2015},
  { ext n,
    split,
    { intro hn,
      obtain ⟨h₁, h₂, m, h₃, h₄⟩ := h₀ n hn,
      rw h₂ m h₃ at h₄,
      interval_cases n; try { contradiction },
      { use 11, norm_num },
      { use 15, norm_num } },
    { intro hn,
      simp only [mem_insert, mem_singleton] at hn,
      cases hn; subst hn,
      { use 11, norm_num },
      { use 15, norm_num } } },

  rw h₃,
  norm_num,
end