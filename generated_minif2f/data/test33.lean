import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

theorem min_x_for_conditions (x y : ℕ) (hx : x % 3 = 2) (hy : y % 5 = 4) (hxy : x % 10 = y % 10) : 14 ≤ x := by
  -- Express x in terms of a: x = 3a + 2
  have hx' : ∃ a, x = 3 * a + 2 := Nat.exists_eq_add_of_lt hx (by norm_num)
  -- Express y in terms of b: y = 5b + 4
  have hy' : ∃ b, y = 5 * b + 4 := Nat.exists_eq_add_of_lt hy (by norm_num)
  -- Use the condition x % 10 = y % 10
  obtain ⟨a, rfl⟩ := hx'
  obtain ⟨b, rfl⟩ := hy'
  have hxy' : (3 * a + 2) % 10 = (5 * b + 4) % 10 := hxy
  -- Simplify the congruence
  have : (3 * a + 2) % 10 = (5 * b + 4) % 10 := hxy'
  have hmod : (3 * a + 2) % 10 = (5 * b + 4) % 10 := this
  -- Solve the congruence
  have : 3 * a + 2 ≡ 5 * b + 4 [MOD 10] := by rw [Nat.modeq_iff_dvd, Nat.dvd_add_iff_right]; exact hmod
  have : 3 * a ≡ 2 [MOD 10] := by linarith
  have : 3 * a ≡ 2 [MOD 10] := this
  -- Find the smallest a such that 3a ≡ 2 [MOD 10]
  have : ∃ a, 3 * a ≡ 2 [MOD 10] := ⟨4, by norm_num⟩
  obtain ⟨a, ha⟩ := this
  -- Calculate x = 3a + 2
  have : x = 3 * a + 2 := by rw [hx']
  have : x = 3 * 4 + 2 := by rw [ha]
  have : x = 14 := by norm_num
  -- Conclude that x ≥ 14
  linarith