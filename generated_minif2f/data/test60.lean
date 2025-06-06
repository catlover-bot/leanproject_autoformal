import Mathlib.Data.Int.Basic

theorem integer_equation_solution (x y : ℤ) :
  y^2 + 3 * (x^2 * y^2) = 30 * x^2 + 517 → 3 * (x^2 * y^2) = 588 :=
begin
  intro h,
  have h1 : 3 * (x^2 * y^2) = 30 * x^2 + 517 - y^2,
  { linarith },
  have h2 : 3 * (x^2 * y^2) = 588,
  { rw h1,
    linarith },
  exact h2,
end