import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset

open Finset

theorem arithmetic_sequence_sum (a d : ℝ) :
  (∑ k in range 5, (a + k * d) = 70) →
  (∑ k in range 10, (a + k * d) = 210) →
  a = 42 / 5 :=
begin
  intros h₀ h₁,
  simp [sum_range_succ, mul_comm d] at h₀ h₁,
  have h₀' : 5 * a + 10 * d = 70 := by linarith,
  have h₁' : 10 * a + 45 * d = 210 := by linarith,
  linarith,
end