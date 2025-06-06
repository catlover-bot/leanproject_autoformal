import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RationalProof

theorem rational_theorem (a b c d : ℚ) :
  (3 * a = b + c + d) →
  (4 * b = a + c + d) →
  (2 * c = a + b + d) →
  (8 * a + 10 * b + 6 * c = 24) →
  (↑d.denom + d.num = 28) :=
begin
  intros h1 h2 h3 h4,
  have h5 : 8 * a + 10 * b + 6 * c = 24 := h4,
  have h6 : 3 * a = b + c + d := h1,
  have h7 : 4 * b = a + c + d := h2,
  have h8 : 2 * c = a + b + d := h3,
  linarith,
end

end RationalProof