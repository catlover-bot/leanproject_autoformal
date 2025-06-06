import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

theorem product_bound (n : ℕ) (h : 0 < n) : 
  ∏ k in Icc 1 n, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / n :=
begin
  induction n with m ih,
  { exfalso, exact Nat.not_lt_zero 0 h },
  { cases m,
    { simp },
    { have h_pos : 0 < m.succ.succ := Nat.succ_pos _,
      have ih' := ih (Nat.succ_pos _),
      rw [prod_range_succ, Nat.succ_eq_add_one],
      have : (1 + 1 / (m.succ.succ : ℝ)^3) ≤ 1 + 1 / (m.succ.succ : ℝ),
      { apply add_le_add_left,
        apply one_div_le_one_div_of_le,
        { exact pow_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) 3 },
        { exact pow_le_pow_of_le_left (Nat.cast_nonneg _) (Nat.le_succ _) 3 } },
      calc
        ∏ (k : ℕ) in Icc 1 m.succ.succ, (1 + 1 / (k:ℝ)^3)
            = (∏ (k : ℕ) in Icc 1 m.succ, (1 + 1 / (k:ℝ)^3)) * (1 + 1 / (m.succ.succ:ℝ)^3) : by rw prod_range_succ
        ... ≤ (3 - 1 / (m.succ:ℝ)) * (1 + 1 / (m.succ.succ:ℝ)^3) : mul_le_mul ih' this (by norm_num) (by norm_num)
        ... ≤ 3 - 1 / (m.succ.succ:ℝ) : by linarith } }
end