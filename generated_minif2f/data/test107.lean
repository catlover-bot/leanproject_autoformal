import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Real

theorem sqrt_inequality (x : ℝ) (h1 : 0 ≤ 3 - x) (h2 : 0 ≤ x + 1) 
  (h3 : 1 / 2 < sqrt (3 - x) - sqrt (x + 1)) : 
  -1 ≤ x ∧ x < 1 - sqrt 31 / 8 :=
begin
  have h4 : sqrt (3 - x) > sqrt (x + 1) + 1 / 2,
  { linarith },
  have h5 : 3 - x > (sqrt (x + 1) + 1 / 2)^2,
  { apply (sqrt_lt (by linarith) (by linarith)).mp h4 },
  have h6 : 3 - x > x + 1 + x + 1 / 2 + 1 / 4,
  { ring_nf at h5, linarith },
  have h7 : 3 - x > 2x + 5 / 4,
  { linarith },
  have h8 : 3 > 3x + 5 / 4,
  { linarith },
  have h9 : 12 > 12x + 5,
  { linarith },
  have h10 : 7 > 12x,
  { linarith },
  have h11 : 7 / 12 > x,
  { linarith },
  have h12 : x < 1 - sqrt 31 / 8,
  { linarith [h11, show (1 - sqrt 31 / 8) > 7 / 12, by norm_num] },
  have h13 : -1 ≤ x,
  { linarith },
  exact ⟨h13, h12⟩,
end