import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Nat

theorem divisible_by_12 : ∀ (n : ℕ), 12 ∣ 4^(n+1) + 20 :=
begin
  intro n,
  induction n with k hk,
  { -- Base case: n = 0
    norm_num, },
  { -- Inductive step: assume the hypothesis holds for k, prove for k+1
    rw [pow_succ, mul_comm 4, ←add_assoc],
    have h : 12 ∣ 4 * (4^(k+1) + 20) - 60,
    { apply dvd_of_dvd_add_mul_left,
      exact hk, },
    convert h,
    ring, }
end