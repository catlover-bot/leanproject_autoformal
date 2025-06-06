import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric

open Real

theorem cubic_root_cosines (a b c : ℝ) (f : ℝ → ℝ) :
  (∀ x, f x = x^3 + a * x^2 + b * x + c) →
  (f⁻¹' {0} = {cos (2 * pi / 7), cos (4 * pi / 7), cos (6 * pi / 7)}) →
  a * b * c = 1 / 32 :=
begin
  intros hf hroots,
  have h1 : f (cos (2 * pi / 7)) = 0, from set.mem_preimage.mp (set.mem_of_mem_insert (cos (2 * pi / 7)) hroots),
  have h2 : f (cos (4 * pi / 7)) = 0, from set.mem_preimage.mp (set.mem_of_mem_insert_of_mem (cos (4 * pi / 7)) (set.mem_insert_of_mem _ (set.mem_singleton _))),
  have h3 : f (cos (6 * pi / 7)) = 0, from set.mem_preimage.mp (set.mem_of_mem_insert_of_mem (cos (6 * pi / 7)) (set.mem_insert_of_mem _ (set.mem_singleton _))),
  have hsum : cos (2 * pi / 7) + cos (4 * pi / 7) + cos (6 * pi / 7) = -a,
  { rw [hf (cos (2 * pi / 7)), hf (cos (4 * pi / 7)), hf (cos (6 * pi / 7))],
    ring_nf at h1 h2 h3,
    linarith },
  have hprod : cos (2 * pi / 7) * cos (4 * pi / 7) * cos (6 * pi / 7) = -c,
  { rw [hf (cos (2 * pi / 7)), hf (cos (4 * pi / 7)), hf (cos (6 * pi / 7))],
    ring_nf at h1 h2 h3,
    linarith },
  have hsumprod : cos (2 * pi / 7) * cos (4 * pi / 7) + cos (4 * pi / 7) * cos (6 * pi / 7) + cos (6 * pi / 7) * cos (2 * pi / 7) = b,
  { rw [hf (cos (2 * pi / 7)), hf (cos (4 * pi / 7)), hf (cos (6 * pi / 7))],
    ring_nf at h1 h2 h3,
    linarith },
  have hcos : cos (2 * pi / 7) * cos (4 * pi / 7) * cos (6 * pi / 7) = 1 / 8,
  { norm_num },
  rw [hprod, hcos] at hprod,
  rw [← hsum, ← hsumprod, ← hprod],
  ring_nf,
  norm_num,
end