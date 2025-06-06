import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

theorem cos_identity : cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1 / 2 :=
begin
  have h1 : cos (π / 7) + cos (3 * π / 7) + cos (5 * π / 7) = 0,
  { rw [cos_add, cos_add, cos_add, cos_pi_div_seven, cos_two_pi_div_seven, cos_three_pi_div_seven],
    ring },
  have h2 : cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7) = 0,
  { rw [cos_add, cos_add, cos_add, cos_two_pi_div_seven, cos_four_pi_div_seven, cos_six_pi_div_seven],
    ring },
  have h3 : cos (5 * π / 7) = -cos (2 * π / 7),
  { rw [cos_sub, cos_pi, cos_two_pi_div_seven],
    ring },
  have h4 : cos (6 * π / 7) = -cos (π / 7),
  { rw [cos_sub, cos_pi, cos_pi_div_seven],
    ring },
  have h5 : cos (4 * π / 7) = -cos (3 * π / 7),
  { rw [cos_sub, cos_pi, cos_three_pi_div_seven],
    ring },
  linarith [h1, h2, h3, h4, h5],
end