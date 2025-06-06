import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset
open BigOperators

lemma sum_zmod_inverse (p : ℕ) (hp : nat.prime p) (h7 : 7 ≤ p) :
  ∑ k in Icc 1 (p-2), ((k : zmod p)⁻¹ * ((k : zmod p) + 1)⁻¹) = 2 :=
begin
  have hp' : (p : zmod p) = 0 := zmod.nat_cast_self p,
  have h1 : (1 : zmod p) ≠ 0,
  { intro h, rw [← zmod.nat_cast_zero, zmod.nat_cast_inj] at h, linarith, },
  have h2 : (2 : zmod p) ≠ 0,
  { intro h, rw [← zmod.nat_cast_zero, zmod.nat_cast_inj] at h, linarith, },
  have h3 : (p - 1 : zmod p) = -1,
  { rw [← zmod.nat_cast_sub, hp', sub_zero, zmod.nat_cast_one, neg_one_eq_neg_one], },
  have h4 : (p - 2 : zmod p) = -2,
  { rw [← zmod.nat_cast_sub, hp', sub_zero, zmod.nat_cast_two, neg_eq_neg_one_mul, neg_one_eq_neg_one], },
  have h5 : ∀ k ∈ Icc 1 (p-2), ((k : zmod p)⁻¹ * ((k : zmod p) + 1)⁻¹) = (p - k : zmod p)⁻¹ * ((p - k : zmod p) + 1)⁻¹,
  { intros k hk,
    have hk1 : (k : zmod p) ≠ 0,
    { intro h, rw [← zmod.nat_cast_zero, zmod.nat_cast_inj] at h, linarith, },
    have hk2 : ((k : zmod p) + 1) ≠ 0,
    { intro h, rw [← zmod.nat_cast_zero, zmod.nat_cast_inj] at h, linarith, },
    rw [← inv_eq_inv_iff_mul_eq_one, ← inv_eq_inv_iff_mul_eq_one],
    { ring_nf, rw [add_comm, ← sub_eq_add_neg, sub_self, zero_mul, zero_add, one_mul], },
    { exact hk1, },
    { exact hk2, }, },
  have h6 : ∑ k in Icc 1 (p-2), ((k : zmod p)⁻¹ * ((k : zmod p) + 1)⁻¹) = ∑ k in Icc 1 (p-2), (p - k : zmod p)⁻¹ * ((p - k : zmod p) + 1)⁻¹,
  { apply sum_congr rfl, exact h5, },
  rw [h6, sum_Icc_add, sum_Icc_sub, h3, h4],
  { ring_nf, },
  { linarith, },
  { linarith, },
end