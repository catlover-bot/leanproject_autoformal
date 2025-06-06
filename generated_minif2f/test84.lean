import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import Mathlib.Algebra.BigOperators

open Finset

lemma prod_ineq (n : ℕ) (h : 0 < n) : ∏ k in Icc 1 n, (1 + (1:ℝ) / 2^k) < 5 / 2 :=
begin
  have h₁ : ∏ k in Icc 1 n, (1 + (1:ℝ) / 2^k) ≤ 2,
  { induction n with n ih,
    { exfalso, exact Nat.not_lt_zero 0 h },
    { cases n,
      { simp },
      { rw Icc_succ_right,
        rw prod_insert,
        { have : (1 + (1:ℝ) / 2^(n + 1)) ≤ 3 / 2,
          { apply add_le_add_left,
            apply div_le_of_le_mul,
            { norm_num },
            { norm_num } },
          apply mul_le_mul,
          { exact this },
          { exact ih (Nat.succ_pos n) },
          { norm_num },
          { norm_num } },
        { exact Nat.succ_ne_self n } } } },
  linarith,
end

theorem main_theorem : ∀ (n : ℕ), 0 < n → ∏ k in Icc 1 n, (1 + (1:ℝ) / 2^k) < 5 / 2 :=
prod_ineq