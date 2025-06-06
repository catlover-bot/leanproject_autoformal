import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem power_mod_last_digit : (2^2010) % 10 = 4 := by
  have cycle : ∀ n, (2^n) % 10 = [0, 2, 4, 8, 6].get! (n % 4) := by
    intro n
    induction n using Nat.strong_induction_on with n ih
    cases n % 4 with
    | 0 => norm_num
    | 1 => norm_num
    | 2 => norm_num
    | 3 => norm_num
  have h : 2010 % 4 = 2 := by norm_num
  rw [cycle 2010, h]
  norm_num