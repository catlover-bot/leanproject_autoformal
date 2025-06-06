import data.equiv.basic

theorem equiv_apply_twice (σ : equiv ℝ ℝ) (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 :=
begin
  rw h,
  exact σ.apply_symm_apply 2,
end