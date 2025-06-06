import Mathlib.Data.Equiv.Basic

theorem equiv_apply_eq {σ : Equiv ℝ ℝ} (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 :=
begin
  have h1 : σ.2 (σ.1 2) = 2,
  { rw [←h, Equiv.apply_symm_apply] },
  rw [←h1, Equiv.symm_apply_apply],
end