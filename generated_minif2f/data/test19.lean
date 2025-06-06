```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

open Real

lemma logb_eq_of_logb_eq {a b c : ℝ} (h : logb a b = logb a c) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) : b = c :=
begin
  apply_fun (λ x, a ^ x) at h,
  rw [logb_eq_log_div_log, logb_eq_log_div_log] at h,
  rw [← exp_log hb, ← exp_log hc],
  exact (exp_injective (log_pos ha)).1 h,
end

theorem digits_sum_eq_13 (n : ℕ) (h₀ : 0 < n) (h₁ : logb 2 (logb 16 n) = logb 4 (logb 4 n)) : (nat.digits 10 n).sum = 13 :=
begin
  have h₂ : logb 16 n = logb 4 n,
  { apply logb_eq_of_logb_eq h₁,
    { norm_num },
    { apply logb_pos,
      norm_num,
      exact_mod_cast h₀ },
    { apply logb_pos,
      norm_num,
      exact_mod_cast h₀ } },
  have h₃ : n = 16,
  { apply logb_eq_of_logb_eq h₂,
    { norm_num },
    { exact_mod_cast h₀ },
    { exact_mod_cast h₀ } },
  rw h₃,
  norm_num,
end
```