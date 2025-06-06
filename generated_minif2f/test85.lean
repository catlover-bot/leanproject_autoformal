import Mathlib.Data.Real.Basic

theorem complete_the_square (x y : ℝ) : x^2 + 8 * x + y^2 - 6 * y = 0 → (x + 4)^2 + (y - 3)^2 = 5^2 :=
begin
  intro h,
  have h1 : x^2 + 8 * x = (x + 4)^2 - 16, by ring,
  have h2 : y^2 - 6 * y = (y - 3)^2 - 9, by ring,
  rw [h1, h2] at h,
  linarith,
end