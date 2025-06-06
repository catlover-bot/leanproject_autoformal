import data.equiv.basic

theorem mathd_algebra_209
(σ : equiv ℝ ℝ)
(h₀ : σ.2 2 = 10)
(h₁ : σ.2 10 = 1)
(h₂ : σ.2 1 = 2) :
σ.1 (σ.1 10) = 1 :=
begin
  -- From h₀: σ.2 2 = 10, we have σ.1 10 = 2
  have h₃ : σ.1 10 = 2, from equiv.apply_eq_iff_eq_symm_apply.mpr h₀,
  -- From h₂: σ.2 1 = 2, we have σ.1 2 = 1
  have h₄ : σ.1 2 = 1, from equiv.apply_eq_iff_eq_symm_apply.mpr h₂,
  -- Substitute these into σ.1 (σ.1 10)
  rw [h₃, h₄],
end