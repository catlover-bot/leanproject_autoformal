import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Int

theorem odd_square_mod_eight (a : ℤ) (b : ℕ) (ha : Odd a) (hb : 4 ∣ b) : (a^2 + b^2) % 8 = 1 := 
  by
  -- Express a as an odd integer
  obtain ⟨k, hk⟩ := ha
  have ha2 : a^2 % 8 = 1 := by
    rw [hk]
    calc
      (2 * k + 1)^2 = 4 * k^2 + 4 * k + 1 := by ring
      _ % 8 = 1 := by norm_num

  -- Express b as a multiple of 4
  obtain ⟨m, hm⟩ := hb
  have hb2 : b^2 % 8 = 0 := by
    rw [hm]
    calc
      (4 * m)^2 = 16 * m^2 := by ring
      _ % 8 = 0 := by norm_num

  -- Combine results
  calc
    (a^2 + b^2) % 8 = (a^2 % 8 + b^2 % 8) % 8 := by exact_mod_cast Int.add_mod _ _ _
    _ = (1 + 0) % 8 := by rw [ha2, hb2]
    _ = 1 := by norm_num