import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem power_mod_10 : (16^17 * 17^18 * 18^19) % 10 = 8 := by
  have h1 : 16^17 % 10 = 6 := by
    have cycle_16 : [16^1 % 10, 16^2 % 10, 16^3 % 10, 16^4 % 10] = [6, 6, 6, 6] := by norm_num
    exact cycle_16.get (17 % 4)
  have h2 : 17^18 % 10 = 1 := by
    have cycle_17 : [17^1 % 10, 17^2 % 10, 17^3 % 10, 17^4 % 10] = [7, 9, 3, 1] := by norm_num
    exact cycle_17.get (18 % 4)
  have h3 : 18^19 % 10 = 8 := by
    have cycle_18 : [18^1 % 10, 18^2 % 10, 18^3 % 10, 18^4 % 10] = [8, 4, 2, 6] := by norm_num
    exact cycle_18.get (19 % 4)
  calc
    (16^17 * 17^18 * 18^19) % 10
        = ((16^17 % 10) * (17^18 % 10) * (18^19 % 10)) % 10 := by rw [Nat.mul_mod, Nat.mul_mod]
    _ = (6 * 1 * 8) % 10 := by rw [h1, h2, h3]
    _ = 48 % 10 := by norm_num
    _ = 8 := by norm_num