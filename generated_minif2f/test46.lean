import data.nat.basic
import data.nat.divisors
import data.finset
import algebra.big_operators

open finset
open_locale big_operators

theorem mathd_numbertheory_451
(S : finset ℕ)
(h₀ : ∀ (n : ℕ), n ∈ S ↔ 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, ((nat.divisors m).card = 4 ∧ ∑ p in (nat.divisors m), p = n)) :
∑ k in S, k = 2016 :=
begin
  have h₁ : S = {2010, 2016, 2018},
  { ext n,
    simp only [mem_insert, mem_singleton, mem_filter, mem_range, h₀, and_assoc, exists_prop, and_comm (n ≤ 2019)],
    split,
    { rintro ⟨h₁, h₂, m, h₃, h₄⟩,
      have : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 14 ∨ m = 15 ∨ m = 21,
      { rcases h₃ with ⟨h₃₁, h₃₂⟩,
        fin_cases h₃₁,
        { exact or.inl rfl },
        { exact or.inr (or.inl rfl) },
        { exact or.inr (or.inr (or.inl rfl)) },
        { exact or.inr (or.inr (or.inr (or.inl rfl))) },
        { exact or.inr (or.inr (or.inr (or.inr (or.inl rfl)))) },
        { exact or.inr (or.inr (or.inr (or.inr (or.inr rfl)))) } },
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl;
      simp [nat.divisors, nat.divisors_eq_filter_dvd, nat.divisors_filter, nat.divisors_card, nat.divisors_sum] at h₄;
      try { linarith } },
    { rintro (rfl | rfl | rfl);
      use [6, 8, 10, 14, 15, 21];
      simp [nat.divisors, nat.divisors_eq_filter_dvd, nat.divisors_filter, nat.divisors_card, nat.divisors_sum];
      try { linarith } } },
  rw h₁,
  simp,
end