import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset

lemma sum_sqrt_reciprocal_bound : ∑ k in (Icc (2 : ℕ) 10000), (1 / real.sqrt k) < 198 :=
begin
  have h₁ : ∑ k in (Icc (2 : ℕ) 10000), (1 / real.sqrt k) < ∑ k in (Icc (2 : ℕ) 10000), (1 / real.sqrt 2),
  { apply sum_lt_sum,
    { intros x hx,
      rw mem_Icc at hx,
      exact one_div_lt_one_div_of_lt (real.sqrt_pos.mpr (nat.cast_pos.mpr hx.1)) (real.sqrt_lt_sqrt (nat.cast_lt.mpr hx.1) (nat.cast_lt.mpr hx.2)) },
    { use 2,
      rw [mem_Icc, le_refl, nat.succ_le_iff],
      exact nat.succ_pos' } },
  have h₂ : ∑ k in (Icc (2 : ℕ) 10000), (1 / real.sqrt 2) = (9999 : ℝ) * (1 / real.sqrt 2),
  { rw sum_const,
    simp },
  have h₃ : (9999 : ℝ) * (1 / real.sqrt 2) < 198,
  { norm_num,
    rw [mul_div_assoc, div_lt_iff],
    { norm_num },
    { exact real.sqrt_pos.mpr (by norm_num) } },
  linarith,
end