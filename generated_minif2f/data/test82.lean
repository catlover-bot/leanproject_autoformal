import Mathlib.Data.Complex.Basic

open Complex

theorem complex_solution (f z : ℂ) :
  (f + 3 * z = 11) → (3 * (f - 1) - 5 * z = -68) → (f = -10 ∧ z = 7) :=
begin
  intros h1 h2,
  have h3 : f = 11 - 3 * z, from eq_sub_of_add_eq h1,
  rw h3 at h2,
  have h4 : 3 * ((11 - 3 * z) - 1) - 5 * z = -68, from h2,
  simp at h4,
  have h5 : 30 - 9 * z - 5 * z = -68, from h4,
  simp at h5,
  have h6 : 30 - 14 * z = -68, from h5,
  linarith,
  have hz : z = 7, from (eq_of_sub_eq_zero (by linarith : 14 * z - 98 = 0)),
  have hf : f = 11 - 3 * 7, from h3,
  simp at hf,
  exact ⟨hf, hz⟩,
end