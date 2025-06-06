import Mathlib.Data.Real.Basic

lemma linear_function_evaluation (f : ℝ → ℝ) (h : ∀ x, f x = 5 * x + 4) : f 1 = 9 :=
by rw [h 1]; norm_num