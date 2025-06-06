import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational

open Real

theorem exists_irrational_a_b_not_irrational_a_pow_b : ∃ a b, irrational a ∧ irrational b ∧ ¬ irrational (a^b) :=
  let a := Real.sqrt 2
  let b := Real.sqrt 2
  have ha : irrational a := irrational_sqrt_two
  have hb : irrational b := irrational_sqrt_two
  have h : a^b = 2 := by
    rw [←Real.rpow_mul (sqrt_nonneg 2) (sqrt_nonneg 2)]
    norm_num
  use a, b
  refine ⟨ha, hb, _⟩
  rw [h]
  exact not_irrational_two