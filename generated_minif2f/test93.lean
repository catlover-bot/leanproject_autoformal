import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem power_equation_solution : ∀ (a b : ℝ), (2:ℝ)^a = 32 → a^b = 125 → b^a = 243 :=
begin
  intros a b h1 h2,
  have ha : a = 5,
  { rw [←Real.rpow_nat_cast, Real.rpow_eq_rpow_iff] at h1,
    exact h1.1,
    norm_num },
  have hb : b = 3,
  { rw [ha] at h2,
    rw [←Real.rpow_nat_cast, Real.rpow_eq_rpow_iff] at h2,
    exact h2.1,
    norm_num },
  rw [ha, hb],
  norm_num,
end