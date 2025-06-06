import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace FibonacciMod4

theorem fibonacci_mod_4 (a : ℕ → ℕ) (h1 : a 1 = 1) (h2 : a 2 = 1) (h3 : ∀ n, a (n + 2) = a (n + 1) + a n) : a 100 % 4 = 3 := by
  have h4 : ∀ n, a (n + 1) % 4 = (a n % 4 + a (n - 1) % 4) % 4 := by
    intro n
    cases n
    · rw [h1, h2]
      norm_num
    · rw [h3 n]
      exact Nat.add_mod _ _ 4
  have h5 : ∀ n, a n % 4 = match n % 6 with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | 3 => 2
    | 4 => 3
    | 5 => 3 := by
    intro n
    induction n using Nat.strong_induction_on with n ih
    cases n % 6 with
    | 0 =>
      cases n
      · norm_num
      · rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))]
        rw [h3 (n - 1), ih (n - 1) (Nat.sub_lt (Nat.succ_pos _) (Nat.succ_pos _)), ih (n - 2) (Nat.sub_lt (Nat.succ_pos _) (Nat.succ_pos _))]
        norm_num
    | 1 => rw [h1]; norm_num
    | 2 => rw [h2]; norm_num
    | 3 =>
      rw [h3 1, h1, h2]
      norm_num
    | 4 =>
      rw [h3 2, h2, h3 1, h1, h2]
      norm_num
    | 5 =>
      rw [h3 3, h3 2, h2, h3 1, h1, h2]
      norm_num
  have h6 : 100 % 6 = 4 := by norm_num
  rw [h5 100, h6]
  norm_num

end FibonacciMod4