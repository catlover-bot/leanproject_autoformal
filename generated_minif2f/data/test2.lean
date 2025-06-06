import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

open Int

theorem no_solution_for_4x3_minus_7y3_eq_2003 : ∀ (x y : ℤ), 4 * x^3 - 7 * y^3 ≠ 2003 := by
  intro x y
  intro hneq
  apply_fun (coe : ℤ → ZMod 7) at hneq
  push_cast at hneq
  have : (2003 : ZMod 7) = 1 := by decide
  rw [this] at hneq
  have : (7 : ZMod 7) = 0 := by decide
  rw [this, zero_mul, sub_zero] at hneq
  have main : ∀ (x : ZMod 7), x^3 = 0 ∨ x^3 = 1 ∨ x^3 = -1 := by
    intro x
    fin_cases x using Finite
    all_goals decide
  rcases main (x : ZMod 7) with h' | h' | h'
  · rw [h'] at hneq
    decide at hneq
  · rw [h'] at hneq
    decide at hneq
  · rw [h'] at hneq
    decide at hneq
  contradiction