import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

theorem am_gm_inequality_variant (a b : ℝ) (h : 0 < a ∧ 0 < b) (h_le : b ≤ a) :
  (a + b) / 2 - sqrt (a * b) ≤ (a - b)^2 / (8 * b) :=
begin
  have h1 : (a + b) / 2 - sqrt (a * b) = ((a - b)^2) / (2 * ((a + b) / 2 + sqrt (a * b))),
  { have h2 : (a + b) / 2 = (a + b) / 2, by refl,
    have h3 : sqrt (a * b) = sqrt (a * b), by refl,
    rw [h2, h3],
    field_simp [h.1.ne', h.2.ne'],
    ring },
  rw h1,
  have h4 : 2 * ((a + b) / 2 + sqrt (a * b)) ≥ 8 * b,
  { apply mul_le_mul_of_nonneg_left,
    { linarith [sqrt_le_iff.mpr ⟨mul_nonneg h.1.le h.2.le, mul_le_mul h_le le_rfl h.2.le h.1.le⟩] },
    norm_num },
  apply div_le_div_of_le h4,
  ring_nf,
  linarith,
end