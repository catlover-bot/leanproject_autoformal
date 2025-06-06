import Mathlib.Data.Real.Basic

theorem solve_system (x y z : ℝ) :
  (3 * x + y = 17) → (5 * y + z = 14) → (3 * x + 5 * z = 41) → (x + y + z = 12) :=
begin
  intros h1 h2 h3,
  have h4 : 3 * x + 6 * y + z = 31,
  { linarith },
  have h5 : 6 * y - 4 * z = -10,
  { linarith },
  have h6 : 3 * y - 2 * z = -5,
  { linarith },
  have h7 : y = 2,
  { linarith },
  have h8 : z = 3.5,
  { linarith },
  have h9 : x = 6.5,
  { linarith },
  linarith,
end