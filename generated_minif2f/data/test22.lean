import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Linarith

namespace MyNamespace

open Int

theorem no_solution (x y : ℤ) : x^5 ≠ y^2 + 4 := by
  intro h
  have h1 : x^5 ≡ y^2 + 4 [ZMOD 5] := by
    rw [h]
  have h2 : x^5 ≡ x [ZMOD 5] := by
    apply pow_mod
    norm_num
  have h3 : y^2 + 4 ≡ y^2 - 1 [ZMOD 5] := by
    norm_num
  have h4 : x ≡ y^2 - 1 [ZMOD 5] := by
    linarith
  have h5 : x^5 ≡ (y^2 - 1)^5 [ZMOD 5] := by
    rw [h4]
  have h6 : (y^2 - 1)^5 ≡ y^2 - 1 [ZMOD 5] := by
    apply pow_mod
    norm_num
  linarith

end MyNamespace