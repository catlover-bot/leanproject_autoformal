import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem cube_root_expression (a : ℝ) (h₀ : a = 8) : (16 * (a^2)^((1:ℝ) / 3))^((1:ℝ) / 3) = 4 :=
by
  rw [h₀]  -- Substitute a = 8
  have h₁ : (8^2 : ℝ) = 64 := by norm_num
  rw [h₁]
  have h₂ : (64 : ℝ) = (4^3 : ℝ) := by norm_num
  rw [h₂]
  have h₃ : (16 : ℝ) = (4^2 : ℝ) := by norm_num
  rw [h₃]
  have h₄ : (4^2 * (4^3)^((1:ℝ) / 3))^((1:ℝ) / 3) = (4^(2 + 1))^((1:ℝ) / 3) := by
    rw [rpow_mul (4^3) ((1:ℝ) / 3) ((1:ℝ) / 3)]
    rw [rpow_nat_cast]
    rw [rpow_nat_cast]
    rw [mul_assoc]
  rw [h₄]
  have h₅ : (4^(2 + 1))^((1:ℝ) / 3) = 4 := by
    rw [rpow_nat_cast]
    rw [rpow_mul (4^3) ((1:ℝ) / 3) ((1:ℝ) / 3)]
    rw [rpow_nat_cast]
    norm_num
  rw [h₅]
  norm_num