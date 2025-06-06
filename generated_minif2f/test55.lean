import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem pow_mod_ten : (2^2010) % 10 = 4 := by
  have h : ∀ n, (2^n) % 10 = [1, 2, 4, 8, 6].get! (n % 4) := by
    intro n
    induction n using Nat.strong_induction_on with n ih
    cases n % 4 with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | 3 => norm_num
  exact h 2010