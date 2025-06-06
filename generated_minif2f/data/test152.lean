import Mathlib.Data.Nat.Digits
import Mathlib.Tactic.NormNum

open Nat

theorem digits_sum_5_pow_100_mod_1000 :
  ∀ (a b c : ℕ), (a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9) ∧ nat.digits 10 ((5^100) % 1000) = [c, b, a] → a + b + c = 13 :=
begin
  intros a b c h,
  have h1 : (5^100) % 1000 = 125,
  { norm_num },
  have h2 : nat.digits 10 125 = [5, 2, 1],
  { norm_num },
  rw h1 at h,
  rw h2 at h,
  cases h with _ h_digits,
  injection h_digits with h_c h_b h_a,
  rw [h_a, h_b, h_c],
  norm_num,
end