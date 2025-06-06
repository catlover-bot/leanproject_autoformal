```lean
import data.zmod.basic
import data.nat.prime
import data.finset
import algebra.big_operators

open_locale big_operators
open finset

lemma sum_inverse_pairs (p : ℕ) (hp : nat.prime p) (h7 : 7 ≤ p) :
  ∑ k in Icc 1 (p - 2), ((k : zmod p)⁻¹ * ((k : zmod p) + 1)⁻¹) = 2 :=
begin
  have h1 : ∀ k : ℕ, k ∈ Icc 1 (p - 2) → (k : zmod p) ≠ 0,
  { intros k hk,
    rw [mem_Icc] at hk,
    exact ne_of_gt (nat.cast_pos.2 hk.1) },
  
  have h2 : ∀ k : ℕ, k ∈ Icc 1 (p - 2) → ((k : zmod p) + 1) ≠ 0,
  { intros k hk,
    rw [mem_Icc] at hk,
    have : (k + 1 : ℕ) ≤ p - 1 := nat.succ_le_succ hk.2,
    exact ne_of_lt (nat.cast_lt.2 this) },

  have h3 : ∀ k : ℕ, k ∈ Icc 1 (p - 2) → ((k : zmod p)⁻¹ * ((k : zmod p) + 1)⁻¹) = 1 - (k + 1 : zmod p)⁻¹ * (k : zmod p)⁻¹,
  { intros k hk,
    field_simp [h1 k hk, h2 k hk],
    ring },

  have h4 : ∑ k in Icc 1 (p - 2), (1 : zmod p) = (p - 2 : zmod p),
  { rw [sum_const, card_Icc, nat.cast_sub, nat.cast_one],
    exact_mod_cast nat.sub_add_cancel (nat.succ_le_iff.2 h7) },

  have h5 : ∑ k in Icc 1 (p - 2), (k + 1 : zmod p)⁻¹ * (k : zmod p)⁻¹ = ∑ k in Icc 1 (p - 2), (k : zmod p)⁻¹ * ((k + 1) : zmod p)⁻¹,
  { apply sum_congr rfl,
    intros k hk,
    rw mul_comm },

  rw [sum_congr rfl h3, sum_sub_distrib, h4, h5],
  have h6 : ∑ k in Icc 1 (p - 2), (k + 1 : zmod p)⁻¹ * (k : zmod p)⁻¹ = 0,
  { rw ← sum_range_succ,
    simp only [nat.cast_add, nat.cast_one, add_right_neg, sum_const_zero] },

  rw [h6, sub_zero],
  exact_mod_cast nat.sub_add_cancel (nat.succ_le_iff.2 h7),
end
```