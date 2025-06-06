import Mathlib.Data.Real.Basic

theorem power_exponents (a b : ℝ) : (2:ℝ)^a = 32 → a^b = 125 → b^a = 243 :=
begin
  intros h1 h2,
  -- Determine a from 2^a = 32
  have ha : a = 5,
  { rw [←Real.rpow_nat_cast, Real.rpow_eq_rpow_iff] at h1,
    exact h1.1,
    norm_num },
  -- Determine b from a^b = 125
  have hb : b = 3,
  { rw ha at h2,
    rw [←Real.rpow_nat_cast, Real.rpow_eq_rpow_iff] at h2,
    exact h2.1,
    norm_num },
  -- Verify b^a = 243
  rw [ha, hb],
  norm_num,
end