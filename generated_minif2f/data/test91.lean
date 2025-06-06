import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

lemma prod_inequality (n : ℕ) (h : 0 < n) : ∏ k in Icc 1 n, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n :=
begin
  induction n with n ih,
  { exfalso, exact nat.not_lt_zero 0 h },
  { cases n,
    { simp },
    { have h_pos : 0 < n.succ.succ := nat.succ_pos _,
      have h_ind : ∏ k in Icc 1 n.succ, (1 + (1:ℝ) / k^3) ≤ 3 - 1 / ↑(n.succ),
      { exact ih (nat.succ_pos _) },
      rw [Icc_succ_right, prod_insert, mul_comm],
      { apply le_trans (mul_le_mul_of_nonneg_right h_ind _),
        { linarith },
        { norm_num, apply div_nonneg, norm_num, apply pow_nonneg, norm_num } },
      { simp } } }
end