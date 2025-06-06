import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

lemma calc_expression : ((100 ^ 2 - 7 ^ 2):ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 :=
by norm_num