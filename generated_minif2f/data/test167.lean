import algebra.big_operators.basic
import data.real.nnreal

open_locale big_operators

theorem prod_le_one_of_sum_eq_n {a : ℕ → nnreal} {n : ℕ} (h : ∑ x in finset.range n, a x = n) :
  ∏ x in finset.range n, a x ≤ 1 :=
begin
  induction n with n ih,
  { simp },
  { rw [finset.sum_range_succ, finset.prod_range_succ] at h ⊢,
    have : a n ≤ 1,
    { rw ← nnreal.coe_le_coe,
      norm_cast,
      linarith },
    exact mul_le_one this (ih h) (zero_le _) }
end