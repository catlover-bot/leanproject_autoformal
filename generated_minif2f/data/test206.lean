import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

open BigOperators

theorem power_mean_inequality (a b : ℝ) (n : ℕ) (h₁ : 0 < a ∧ 0 < b) (h₂ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 :=
begin
  induction n with k hk,
  { exfalso, exact Nat.not_lt_zero _ h₂ },
  { cases k,
    { simp [pow_one] },
    { have h_ind : ((a + b) / 2)^(k.succ) ≤ (a^(k.succ) + b^(k.succ)) / 2 := hk (Nat.succ_pos k),
      calc
        ((a + b) / 2)^(k.succ.succ)
            = ((a + b) / 2) * ((a + b) / 2)^(k.succ) : by rw [pow_succ]
        ... ≤ ((a + b) / 2) * ((a^(k.succ) + b^(k.succ)) / 2) : mul_le_mul_of_nonneg_left h_ind (div_nonneg (add_nonneg (le_of_lt h₁.1) (le_of_lt h₁.2)) zero_le_two)
        ... = ((a + b) * (a^(k.succ) + b^(k.succ))) / 4 : by rw [mul_div_assoc, mul_div_right_comm]
        ... = (a * a^(k.succ) + a * b^(k.succ) + b * a^(k.succ) + b * b^(k.succ)) / 4 : by ring
        ... = (a^(k.succ.succ) + b^(k.succ.succ) + a * b^(k.succ) + b * a^(k.succ)) / 4 : by rw [←pow_succ, ←pow_succ]
        ... ≤ (a^(k.succ.succ) + b^(k.succ.succ) + a^(k.succ.succ) + b^(k.succ.succ)) / 4 : by linarith [h₁.1, h₁.2]
        ... = (a^(k.succ.succ) + b^(k.succ.succ)) / 2 : by ring } }
end