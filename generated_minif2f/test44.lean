import Mathlib.Data.Finset
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset
open BigOperators

lemma sum_mod_10_of_multiples_of_3 : 
  ∑ k in finset.filter (λ x, 3 ∣ x) (finset.Icc 1 49), (k % 10) = 78 :=
begin
  let s := finset.filter (λ x, 3 ∣ x) (finset.Icc 1 49),
  have hs : s = {3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48},
  { ext x,
    simp only [mem_filter, mem_Icc, and_assoc, and_comm (3 ∣ x)],
    split,
    { rintro ⟨⟨hx1, hx2⟩, hx3⟩,
      obtain ⟨k, rfl⟩ := hx3,
      simp only [true_and, le_add_iff_nonneg_right, zero_le, le_of_lt, nat.succ_pos'],
      split,
      { linarith },
      { linarith } },
    { rintro ⟨hx1, hx2⟩,
      refine ⟨⟨hx1, hx2⟩, _⟩,
      use x / 3,
      exact (nat.div_mul_cancel (nat.dvd_of_mod_eq_zero (nat.mod_eq_zero_of_dvd hx2))).symm } },
  rw hs,
  norm_num,
end