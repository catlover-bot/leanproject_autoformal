import Mathlib.Data.Equiv.Basic

theorem mathd_algebra_209
  (σ : Equiv ℝ ℝ)
  (h₀ : σ.symm 2 = 10)
  (h₁ : σ.symm 10 = 1)
  (h₂ : σ.symm 1 = 2) :
  σ (σ 10) = 1 :=
begin
  have h₃ : σ 2 = 1,
  { rw [←Equiv.symm_apply_eq, h₂] },
  have h₄ : σ 10 = 2,
  { rw [←Equiv.symm_apply_eq, h₀] },
  rw [h₄, h₃],
end