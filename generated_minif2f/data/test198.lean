import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue

open Real

theorem amc12a_2002_p13
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a ≠ b)
  (h₂ : abs (a - 1/a) = 1)
  (h₃ : abs (b - 1/b) = 1) :
  a + b = sqrt 5 :=
begin
  have h₄ : a - 1/a = 1 ∨ a - 1/a = -1,
  { rw abs_eq at h₂, exact h₂ },
  have h₅ : b - 1/b = 1 ∨ b - 1/b = -1,
  { rw abs_eq at h₃, exact h₃ },
  cases h₄ with h₄a h₄a;
  cases h₅ with h₅b h₅b;
  { 
    have ha : a^2 - a - 1 = 0,
    { field_simp [h₄a], ring },
    have hb : b^2 - b - 1 = 0,
    { field_simp [h₅b], ring },
    have ha' : a = (1 + sqrt 5) / 2 ∨ a = (1 - sqrt 5) / 2,
    { rw [←sub_eq_zero, ←mul_self_eq_mul_self_iff] at ha,
      field_simp at ha,
      norm_num at ha,
      exact ha },
    have hb' : b = (1 + sqrt 5) / 2 ∨ b = (1 - sqrt 5) / 2,
    { rw [←sub_eq_zero, ←mul_self_eq_mul_self_iff] at hb,
      field_simp at hb,
      norm_num at hb,
      exact hb },
    cases ha' with ha' ha';
    cases hb' with hb' hb';
    { 
      try { exfalso, linarith },
      { field_simp [ha', hb'], ring },
      { field_simp [ha', hb'], ring }
    }
  }
end