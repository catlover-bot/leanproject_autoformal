import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MyNamespace

theorem solve_equation (x y : ℤ) : y^2 + 3 * (x^2 * y^2) = 30 * x^2 + 517 → 3 * (x^2 * y^2) = 588 :=
begin
  intro h,
  linarith,
end

end MyNamespace