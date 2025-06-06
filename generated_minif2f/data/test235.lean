import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Linarith

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 :=
by
  -- We will use a linear combination of h₀, h₁, and h₂ to derive the result.
  -- Specifically, we will use the combination: 6 * h₂ - 5 * h₁ + h₀.
  have h : 6 * h₂ - 5 * h₁ + h₀ = 334 := by
    calc
      6 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g)
      - 5 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g)
      + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g)
      = (54 * a + 96 * b + 150 * c + 216 * d + 294 * e + 384 * f + 486 * g)
      - (20 * a + 45 * b + 80 * c + 125 * d + 180 * e + 245 * f + 320 * g)
      + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) : by ring
    _ = (54 * a - 20 * a + a) + (96 * b - 45 * b + 4 * b) + (150 * c - 80 * c + 9 * c)
        + (216 * d - 125 * d + 16 * d) + (294 * e - 180 * e + 25 * e)
        + (384 * f - 245 * f + 36 * f) + (486 * g - 320 * g + 49 * g) : by ring
    _ = 35 * a + 55 * b + 79 * c + 107 * d + 139 * e + 175 * f + 215 * g : by ring
    _ = 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g : by ring
    _ = 334 : by linarith [h₀, h₁, h₂]
  exact h