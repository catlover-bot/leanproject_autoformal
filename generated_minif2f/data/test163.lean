import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem binomial_inequality (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
  (1 + ↑n * x) ≤ (1 + x)^(n:ℕ) :=
begin
  induction n with k ih,
  { exfalso, exact Nat.not_lt_zero _ h₁ },
  { cases k,
    { simp },
    { have h₂ : (1 + ↑(k.succ) * x) = (1 + ↑k * x + x),
      { ring },
      rw h₂,
      have h₃ : (1 + x)^(k.succ.succ) = (1 + x)^(k.succ) * (1 + x),
      { rw pow_succ },
      rw h₃,
      apply le_trans,
      { apply add_le_add,
        { exact ih },
        { apply le_of_lt,
          exact h₀ } },
      { ring_nf,
        apply mul_le_mul_of_nonneg_right,
        { exact ih },
        { linarith } } } }
end