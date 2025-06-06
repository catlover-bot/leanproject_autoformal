import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational

open Real

theorem exists_irrational_exponentiation_not_irrational : 
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) :=
begin
  let a := Real.sqrt 2,
  have ha : Irrational a := Real.irrational_sqrt_two,
  by_cases h : Irrational (a^a),
  { -- Case 1: Assume (sqrt 2)^(sqrt 2) is irrational
    use [a^a, a],
    split,
    { exact h },
    split,
    { exact ha },
    { rw [← Real.rpow_mul, mul_self_sqrt (le_of_lt (by norm_num : 0 < 2))],
      norm_num,
      exact not_irrational_two } },
  { -- Case 2: (sqrt 2)^(sqrt 2) is not irrational
    use [a, a],
    split,
    { exact ha },
    split,
    { exact ha },
    { exact h } }
end