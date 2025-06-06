```lean
import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

open Nat

lemma digits_5_pow_100_mod_1000 : digits 10 ((5^100) % 1000) = [3, 1, 5] := by
  have h : (5^100) % 1000 = 513 := by norm_num
  rw [h]
  exact digits_of_nat 10 513

theorem sum_of_digits_5_pow_100_mod_1000 (a b c : ℕ) :
  (a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9) ∧ digits 10 ((5^100) % 1000) = [c, b, a] → a + b + c = 13 := by
  intro ⟨⟨ha, hb, hc⟩, h⟩
  have h_digits : digits 10 ((5^100) % 1000) = [3, 1, 5] := digits_5_pow_100_mod_1000
  rw [h] at h_digits
  injection h_digits with hc' hb' ha'
  rw [←hc', ←hb', ←ha']
  norm_num
```