import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupWithZero.Basic

theorem weighted_average (m a : ℕ) (h : 0 < m ∧ 0 < a) 
  (h_ratio : (↑m / ↑a : ℝ) = 3 / 4) : 
  (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = 76 :=
begin
  have h_eq : 4 * (m : ℝ) = 3 * (a : ℝ),
  { rw [div_eq_iff, mul_comm, ← mul_assoc, mul_comm (3 : ℝ)],
    exact h_ratio,
    norm_num },
  have h_m : (m : ℝ) = 3 / 4 * (a : ℝ),
  { rw [← mul_div_assoc, mul_comm, ← div_eq_iff, mul_comm],
    exact h_eq,
    norm_num },
  rw [h_m],
  have h_num : 84 * (3 / 4 * (a : ℝ)) + 70 * (a : ℝ) = 76 * (a : ℝ),
  { ring_nf,
    norm_num },
  have h_den : 3 / 4 * (a : ℝ) + (a : ℝ) = 7 / 4 * (a : ℝ),
  { ring_nf },
  rw [h_num, h_den],
  field_simp [h.2],
  norm_num,
end