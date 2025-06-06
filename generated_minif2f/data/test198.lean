import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

theorem amc12a_2002_p13
(a b : ℝ)
(h₀ : 0 < a ∧ 0 < b)
(h₁ : a ≠ b)
(h₂ : abs (a - 1/a) = 1)
(h₃ : abs (b - 1/b) = 1) :
a + b = real.sqrt 5 :=
begin
  have ha1 : a - 1/a = 1 ∨ a - 1/a = -1,
  { rw abs_eq at h₂, exact h₂ },
  have hb1 : b - 1/b = 1 ∨ b - 1/b = -1,
  { rw abs_eq at h₃, exact h₃ },
  
  cases ha1 with ha_pos ha_neg,
  { -- Case a - 1/a = 1
    have ha_eq : a^2 - a - 1 = 0,
    { field_simp [ha_pos], ring },
    cases hb1 with hb_pos hb_neg,
    { -- Case b - 1/b = 1
      have hb_eq : b^2 - b - 1 = 0,
      { field_simp [hb_pos], ring },
      have a_sol : a = (1 + sqrt 5) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.1)),
        field_simp [ha_eq], ring_nf, norm_num },
      have b_sol : b = (1 - sqrt 5) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.2)),
        field_simp [hb_eq], ring_nf, norm_num },
      rw [a_sol, b_sol],
      field_simp, ring_nf, norm_num },
    { -- Case b - 1/b = -1
      have hb_eq : b^2 + b - 1 = 0,
      { field_simp [hb_neg], ring },
      have a_sol : a = (1 + sqrt 5) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.1)),
        field_simp [ha_eq], ring_nf, norm_num },
      have b_sol : b = (sqrt 5 - 1) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.2)),
        field_simp [hb_eq], ring_nf, norm_num },
      rw [a_sol, b_sol],
      field_simp, ring_nf, norm_num } },
  { -- Case a - 1/a = -1
    have ha_eq : a^2 + a - 1 = 0,
    { field_simp [ha_neg], ring },
    cases hb1 with hb_pos hb_neg,
    { -- Case b - 1/b = 1
      have hb_eq : b^2 - b - 1 = 0,
      { field_simp [hb_pos], ring },
      have a_sol : a = (sqrt 5 - 1) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.1)),
        field_simp [ha_eq], ring_nf, norm_num },
      have b_sol : b = (1 + sqrt 5) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.2)),
        field_simp [hb_eq], ring_nf, norm_num },
      rw [a_sol, b_sol],
      field_simp, ring_nf, norm_num },
    { -- Case b - 1/b = -1
      have hb_eq : b^2 + b - 1 = 0,
      { field_simp [hb_neg], ring },
      have a_sol : a = (sqrt 5 - 1) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.1)),
        field_simp [ha_eq], ring_nf, norm_num },
      have b_sol : b = (1 - sqrt 5) / 2,
      { apply eq_of_mul_eq_mul_left (ne_of_gt (h₀.2)),
        field_simp [hb_eq], ring_nf, norm_num },
      rw [a_sol, b_sol],
      field_simp, ring_nf, norm_num } }
end