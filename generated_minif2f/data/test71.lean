import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

lemma pow_mod (a b n : ℕ) : (a^b) % n = (a % n)^b % n := by
  rw [Nat.pow_mod, Nat.mod_mod]

theorem mod_calculation : (129^34 + 96^38) % 11 = 9 := by
  have h1 : 129 % 11 = 8 := by norm_num
  have h2 : 96 % 11 = 8 := by norm_num
  have h3 : (8^34) % 11 = 1 := by norm_num
  have h4 : (8^38) % 11 = 0 := by norm_num
  calc
    (129^34 + 96^38) % 11
        = ((129^34) % 11 + (96^38) % 11) % 11 := by rw [Nat.add_mod]
    _ = (8^34 % 11 + 8^38 % 11) % 11 := by rw [pow_mod, pow_mod, h1, h2]
    _ = (1 + 0) % 11 := by rw [h3, h4]
    _ = 1 % 11 := by norm_num
    _ = 9 := by norm_num