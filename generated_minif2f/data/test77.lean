import data.real.basic
import data.finset
import data.nat.sqrt
import data.int.basic

open finset
open_locale big_operators

theorem card_six (S : finset ℕ) 
  (h : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = int.floor (real.sqrt n)) : 
  S.card = 6 :=
begin
  have h1 : ∀ n ∈ S, 0 < n, from λ n hn, (h n).1 hn,
  have h2 : ∀ n ∈ S, (↑n + (1000 : ℝ)) / 70 = int.floor (real.sqrt n), from λ n hn, (h n).1 hn,
  
  let T := {n : ℕ | 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = int.floor (real.sqrt n)},
  have hT : ∀ n, n ∈ S ↔ n ∈ T, from λ n, h n,
  
  have : S = T.to_finset, from finset.ext hT,
  rw this,
  
  have : T = {n | ∃ k : ℤ, 70 * k - 1000 = n ∧ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = k},
  { ext n,
    split,
    { rintro ⟨hn_pos, hn_eq⟩,
      let k := int.floor (real.sqrt n),
      use k,
      split,
      { rw [← int.cast_inj, int.cast_sub, int.cast_mul, int.cast_coe_nat, int.cast_coe_nat],
        rw [← sub_eq_iff_eq_add, sub_eq_iff_eq_add] at hn_eq,
        exact_mod_cast hn_eq },
      { exact ⟨hn_pos, hn_eq⟩ } },
    { rintro ⟨k, rfl, hn_pos, hn_eq⟩,
      exact ⟨hn_pos, hn_eq⟩ } },
  
  have : T.to_finset = {n | ∃ k : ℤ, 70 * k - 1000 = n ∧ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = k}.to_finset,
  { congr },
  
  have : {n | ∃ k : ℤ, 70 * k - 1000 = n ∧ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = k}.to_finset.card = 6,
  { let ks := {k : ℤ | 70 * k > 1000 ∧ (70 * k - 1000 : ℝ) / 70 = k},
    have : ks = {15, 16, 17, 18, 19, 20},
    { ext k,
      split,
      { rintro ⟨hk1, hk2⟩,
        have : 70 * k - 1000 = 70 * (k - 15) + 50,
        { ring },
        have : 0 ≤ 70 * (k - 15) + 50,
        { linarith },
        have : 70 * (k - 15) + 50 < 70,
        { rw hk2,
          linarith },
        interval_cases k; linarith },
      { rintro (rfl | rfl | rfl | rfl | rfl | rfl);
        split; norm_num } },
    have : ks.to_finset.card = 6,
    { rw this,
      norm_num },
    convert this,
    ext n,
    split,
    { rintro ⟨k, rfl, hn_pos, hn_eq⟩,
      exact ⟨k, ⟨hn_pos, hn_eq⟩⟩ },
    { rintro ⟨k, ⟨hn_pos, hn_eq⟩⟩,
      exact ⟨k, rfl, hn_pos, hn_eq⟩ } },
  
  rw this,
  exact this,
end