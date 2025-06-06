import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem even_n_implies_expression (n : ℕ) (h_even : even n) 
  (h_eq : (↑n - 2)^2 + ↑n^2 + (↑n + 2)^2 = (12296:ℤ)) : 
  ((↑n - 2) * ↑n * (↑n + 2)) / 8 = (32736:ℤ) := 
by
  have h1 : (↑n - 2)^2 + ↑n^2 + (↑n + 2)^2 = (↑n - 2) * (↑n - 2) + ↑n * ↑n + (↑n + 2) * (↑n + 2) := by ring
  rw [h1] at h_eq
  have h2 : (↑n - 2) * (↑n - 2) + ↑n * ↑n + (↑n + 2) * (↑n + 2) = 3 * ↑n^2 + 8 := by ring
  rw [h2] at h_eq
  have h3 : 3 * ↑n^2 + 8 = 12296 := h_eq
  have h4 : 3 * ↑n^2 = 12288 := by linarith
  have h5 : ↑n^2 = 4096 := by linarith
  have h6 : ↑n = 64 := by norm_num at h5; exact Int.eq_of_nat_eq_nat (Nat.sqrt_eq 4096 64 (by norm_num))
  have h7 : ((↑n - 2) * ↑n * (↑n + 2)) / 8 = ((64 - 2) * 64 * (64 + 2)) / 8 := by rw [h6]
  norm_num at h7
  exact h7