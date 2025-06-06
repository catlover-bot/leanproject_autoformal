import Mathlib.Data.Complex.Basic

open Complex

theorem solve_system (f z: ℂ) : (f + 3*z = 11) → (3*(f - 1) - 5*z = -68) → (f = -10 ∧ z = 7) := by
  intros h1 h2
  have eq1 : f = 11 - 3*z := by linarith
  have eq2 : 3*f - 5*z = -65 := by linarith
  rw [eq1] at eq2
  ring_nf at eq2
  have : z = 7 := by linarith
  rw [this] at eq1
  have : f = -10 := by linarith
  exact ⟨this, ‹z = 7›⟩