import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

namespace Proof

theorem solve_for_x (x y : ℕ) (h1 : 0 < x ∧ 0 < y) (h2 : 5 * x = y) (h3 : (↑x - (3:ℤ)) + (y - (3:ℤ)) = 30) : x = 6 := by
  have h4 : ↑x + y = 36 := by
    linarith
  have h5 : 5 * x + x = 36 := by
    rw [←h2] at h4
    exact Int.ofNat.inj h4
  linarith

end Proof