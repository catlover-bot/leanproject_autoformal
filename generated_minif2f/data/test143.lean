import data.nat.factorial
import data.finset
import algebra.big_operators.basic
import algebra.big_operators.finprod

open finset
open_locale big_operators

theorem amc12a_2003_p23
(S : finset ℕ)
(h₀ : ∀ (k : ℕ), k ∈ S ↔ 0 < k ∧ ((k * k) : ℕ) ∣ (∏ i in (finset.Icc 1 9), i!)) :
S.card = 672 :=
begin
  have h_prod : ∏ i in (finset.Icc 1 9), i! = 1! * 2! * 3! * 4! * 5! * 6! * 7! * 8! * 9!,
  { simp },
  have h_val : 1! * 2! * 3! * 4! * 5! * 6! * 7! * 8! * 9! = 13168189440000,
  { norm_num },
  rw h_prod at h₀,
  rw h_val at h₀,
  have h_div : ∀ k, k ∈ S ↔ 0 < k ∧ k * k ∣ 13168189440000,
  { intro k, exact h₀ k },
  have h_sqrt : ∀ k, k ∈ S ↔ 0 < k ∧ k ≤ 3628800,
  { intro k,
    split,
    { intro hk,
      cases hk with hk1 hk2,
      split,
      { exact hk1 },
      { apply nat.le_of_dvd,
        { exact nat.pos_of_ne_zero (ne_of_gt hk1) },
        { exact nat.sqrt_le_self k } } },
    { intro hk,
      cases hk with hk1 hk2,
      split,
      { exact hk1 },
      { apply nat.dvd_of_mod_eq_zero,
        rw [nat.mod_eq_zero_of_dvd, nat.mul_div_cancel_left],
        { exact hk2 },
        { exact nat.pos_of_ne_zero (ne_of_gt hk1) } } } },
  have h_range : S = (finset.Icc 1 3628800).filter (λ k, k * k ∣ 13168189440000),
  { ext k,
    rw [mem_filter, mem_Icc, h_sqrt],
    split,
    { intro hk,
      exact ⟨⟨hk.1, hk.2⟩, hk.2⟩ },
    { intro hk,
      exact ⟨hk.1.1, hk.2⟩ } },
  have h_card : (finset.Icc 1 3628800).filter (λ k, k * k ∣ 13168189440000) = 672,
  { norm_num },
  rw h_range,
  rw h_card,
end