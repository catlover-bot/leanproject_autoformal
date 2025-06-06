import data.finset
import data.nat.digits
import data.nat.parity
import data.nat.prime

open finset
open nat

theorem amc12a_2020_p4
(S : finset ℕ)
(h₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ (d : ℕ), d ∈ nat.digits 10 n → even d) ∧ 5 ∣ n) :
S.card = 100 :=
begin
  let T := (Icc 1000 9999).filter (λ n, (∀ d ∈ digits 10 n, even d) ∧ 5 ∣ n),
  have hT : ∀ n, n ∈ T ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, even d) ∧ 5 ∣ n,
  { intro n, simp [T], },
  have : S = T,
  { ext n, simp [h₀, hT], },
  rw this,
  have h_digits : ∀ n, 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, even d) ∧ 5 ∣ n ↔
    (∃ a b c d, a ∈ {0, 2, 4, 6, 8} ∧ b ∈ {0, 2, 4, 6, 8} ∧ c ∈ {0, 2, 4, 6, 8} ∧ d ∈ {0, 2, 4, 6, 8} ∧
    n = 1000 * a + 100 * b + 10 * c + d ∧ 5 ∣ n),
  { intro n,
    split,
    { rintro ⟨h₁, h₂, h₃, h₄⟩,
      obtain ⟨a, b, c, d, rfl⟩ := digits_eq_of_lt_pow 10 n h₂,
      simp only [digits_def, list.mem_cons_iff, list.mem_singleton, forall_eq_or_imp, forall_eq] at h₃,
      refine ⟨a, b, c, d, h₃.1, h₃.2.1, h₃.2.2.1, h₃.2.2.2, rfl, h₄⟩, },
    { rintro ⟨a, b, c, d, ha, hb, hc, hd, rfl, h₄⟩,
      refine ⟨_, _, _, h₄⟩,
      { linarith [ha, hb, hc, hd], },
      { linarith [ha, hb, hc, hd], },
      { intros d hd,
        simp only [digits_def, list.mem_cons_iff, list.mem_singleton, forall_eq_or_imp, forall_eq] at hd,
        cases hd; assumption, }, }, },
  have : T.card = 5 * 5 * 5 * 4,
  { rw card_eq_sum_ones,
    simp only [h_digits],
    rw sum_sigma',
    simp only [sum_const, card_univ, finset.card_fin, mul_assoc],
    norm_num, },
  rw this,
  norm_num,
end