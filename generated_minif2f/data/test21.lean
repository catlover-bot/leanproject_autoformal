import data.nat.basic
import data.nat.prime
import data.finset
import data.nat.divisors

open nat
open finset

theorem sum_of_prime_divisors_of_500 :
  ∀ (a : ℕ), a = (∑ k in (nat.divisors 500), k) → ∑ k in finset.filter (λ x, nat.prime x) (nat.divisors a), k = 25 :=
begin
  intros a h₀,
  have h₁ : nat.divisors 500 = {1, 2, 4, 5, 10, 20, 25, 50, 100, 125, 250, 500},
  { rw nat.divisors_eq_filter_dvd,
    ext,
    simp [nat.mem_divisors, nat.dvd_iff_mod_eq_zero],
    split,
    { intro h,
      cases h with h₁ h₂,
      exact h₁ },
    { intro h,
      exact ⟨h, nat.pos_of_ne_zero (ne_of_gt (nat.lt_of_le_of_lt (nat.zero_le x) (nat.lt_succ_self 500)))⟩ } },
  have h₂ : a = 1092,
  { rw h₀,
    rw h₁,
    norm_num },
  have h₃ : nat.divisors 1092 = {1, 2, 3, 4, 6, 7, 12, 13, 21, 28, 36, 42, 84, 1092},
  { rw nat.divisors_eq_filter_dvd,
    ext,
    simp [nat.mem_divisors, nat.dvd_iff_mod_eq_zero],
    split,
    { intro h,
      cases h with h₁ h₂,
      exact h₁ },
    { intro h,
      exact ⟨h, nat.pos_of_ne_zero (ne_of_gt (nat.lt_of_le_of_lt (nat.zero_le x) (nat.lt_succ_self 1092)))⟩ } },
  have h₄ : finset.filter (λ x, nat.prime x) (nat.divisors 1092) = {2, 3, 7, 13},
  { rw h₃,
    ext,
    simp [nat.prime],
    split,
    { intro h,
      fin_cases x; norm_num at h },
    { intro h,
      fin_cases x; norm_num } },
  rw h₂,
  rw h₄,
  norm_num,
end