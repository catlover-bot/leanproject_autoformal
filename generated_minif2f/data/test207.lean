import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic

open Real

theorem periodic_function_exists (a : ℝ) (f : ℝ → ℝ) :
  0 < a →
  (∀ x, f (x + a) = 1 / 2 + sqrt (f x - (f x)^2)) →
  ∃ b > 0, ∀ x, f (x + b) = f x :=
begin
  intros ha hf,
  have h_fixed : ∀ x, f x = 1 / 2,
  { intro x,
    have h_eq : f (x + a) = 1 / 2 + sqrt (f x - (f x)^2) := hf x,
    have h_eq' : f (x + 2 * a) = 1 / 2 + sqrt (f (x + a) - (f (x + a))^2) := hf (x + a),
    rw h_eq at h_eq',
    rw h_eq at h_eq',
    have : sqrt (f x - (f x)^2) = 0,
    { linarith },
    have : f x - (f x)^2 = 0,
    { apply sqrt_eq_zero'.mp,
      exact this },
    rw sub_eq_zero at this,
    exact this },
  use a,
  split,
  { exact ha },
  { intro x,
    rw h_fixed x,
    rw h_fixed (x + a) }
end