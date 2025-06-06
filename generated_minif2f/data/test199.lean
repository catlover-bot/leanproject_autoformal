import Mathlib.Algebra.Order.ArithmeticMean
import Mathlib.Data.Real.Basic

open Real

theorem imo_1964_p2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c :=
begin
  let x := a + b - c,
  let y := b + c - a,
  let z := c + a - b,
  have hx : 0 < x := by linarith,
  have hy : 0 < y := by linarith,
  have hz : 0 < z := by linarith,
  have hsum : x + y + z = a + b + c,
  { simp [x, y, z], ring },
  have hxyz : x * y * z = a * b * c,
  { simp [x, y, z], ring },
  have h₄ : a^2 * y ≤ a^2 * (y + z + x) / 3,
  { apply mul_le_mul_of_nonneg_left,
    { apply le_of_lt, apply AM_GM_inequality, exact ⟨hx, hy, hz⟩ },
    { apply pow_nonneg, linarith } },
  have h₅ : b^2 * z ≤ b^2 * (y + z + x) / 3,
  { apply mul_le_mul_of_nonneg_left,
    { apply le_of_lt, apply AM_GM_inequality, exact ⟨hx, hy, hz⟩ },
    { apply pow_nonneg, linarith } },
  have h₆ : c^2 * x ≤ c^2 * (y + z + x) / 3,
  { apply mul_le_mul_of_nonneg_left,
    { apply le_of_lt, apply AM_GM_inequality, exact ⟨hx, hy, hz⟩ },
    { apply pow_nonneg, linarith } },
  calc
    a^2 * y + b^2 * z + c^2 * x
        ≤ a^2 * (y + z + x) / 3 + b^2 * (y + z + x) / 3 + c^2 * (y + z + x) / 3 : by linarith
    ... = (a^2 + b^2 + c^2) * (y + z + x) / 3 : by ring
    ... ≤ (a + b + c)^2 * (y + z + x) / 9 : by { apply mul_le_mul_of_nonneg_right, apply AM_GM_inequality, exact ⟨h₀.1, h₀.2.1, h₀.2.2⟩, linarith }
    ... = (a + b + c) * (a + b + c) * (y + z + x) / 9 : by ring
    ... = (a + b + c) * (a + b + c) * (a + b + c) / 9 : by rw hsum
    ... = (a + b + c)^3 / 9 : by ring
    ... = 3 * a * b * c : by { rw [hxyz, mul_assoc, mul_comm (a * b * c), mul_assoc], ring }
end