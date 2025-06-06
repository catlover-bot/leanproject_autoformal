import data.nat.factorial
import data.finset
import data.nat.prime
import algebra.big_operators

open finset
open_locale big_operators

theorem amc12a_2003_p23
(S : finset ℕ)
(h₀ : ∀ (k : ℕ), k ∈ S ↔ 0 < k ∧ ((k * k) : ℕ) ∣ (∏ i in (finset.Icc 1 9), i!)) :
S.card = 672 :=
begin
  let P := ∏ i in (finset.Icc 1 9), i!,
  have hP : P = 1 * 2 * 6 * 24 * 120 * 720 * 5040 * 40320 * 362880 := rfl,
  have hP' : P = 131681894400 := by norm_num [hP],
  
  have prime_factors : ∀ p, p.prime → p ∣ P → p ∈ {2, 3, 5, 7},
  { intros p hp hdiv,
    have : p ≤ 9 := nat.le_of_dvd (by norm_num) (nat.dvd_of_mem_factors hdiv),
    interval_cases p; norm_num at hp; try { contradiction }; finish },
  
  have factorization : ∀ p, p.prime → p ∣ P → ∃ n, P = p ^ n * (P / p ^ n),
  { intros p hp hdiv,
    use nat.factors_count p P,
    rw [nat.prod_factors, nat.factors_count_eq] },
  
  have eligible_k : ∀ k, 0 < k → (k * k) ∣ P ↔ ∀ p, p.prime → p ∣ k → 2 * nat.factors_count p k ≤ nat.factors_count p P,
  { intros k hk,
    split,
    { intros h p hp hpk,
      have hpk' : p ∣ k * k := dvd_trans hpk (dvd_mul_right p k),
      rw [nat.factors_count_mul, nat.factors_count_mul] at hpk',
      exact nat.le_of_add_le_add_right (nat.le_of_dvd (nat.factors_count_pos_of_dvd hpk') hpk') },
    { intros h,
      rw [nat.dvd_iff_factors_le_factors, nat.factors_mul, nat.factors_mul],
      intros p hp,
      by_cases hpk : p ∣ k,
      { rw [nat.factors_count_mul, nat.factors_count_mul],
        exact le_trans (add_le_add (h p hp hpk) (h p hp hpk)) (le_refl _) },
      { rw [nat.factors_count_eq_zero_of_not_dvd hpk, zero_add],
        exact le_trans (zero_le _) (le_refl _) } } },
  
  have count_k : S.card = 672,
  { rw [← finset.card_univ, ← finset.filter_card_eq],
    apply finset.card_eq_of_bijective,
    { exact λ k hk, k },
    { intros k hk,
      rw [h₀, eligible_k k (finset.mem_univ k)] at hk,
      exact hk },
    { intros a b ha hb hab,
      exact hab },
    { intros b hb,
      use b,
      rw [h₀, eligible_k b (finset.mem_univ b)],
      exact hb } },
  
  exact count_k,
end