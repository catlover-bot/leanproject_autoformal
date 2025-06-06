import Mathlib.Data.Complex.Basic

theorem mathd_algebra_313
  (v i z : ℂ)
  (h₀ : v = i * z)
  (h₁ : v = 1 + complex.I)
  (h₂ : z = 2 - complex.I) :
  i = 1/5 + 3/5 * complex.I :=
by
  rw [h₀, h₁, h₂] at *
  have : i = (1 + complex.I) / (2 - complex.I) := by rw [←div_eq_mul_inv]
  field_simp
  norm_num
  ring_nf
  exact this