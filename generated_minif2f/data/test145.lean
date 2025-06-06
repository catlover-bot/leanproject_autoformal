import Mathlib.Data.Complex.Basic

open Complex

theorem complex_norm_sq_identity (z : ℂ) :
  12 * normSq z = 2 * normSq (z + 2) + normSq (z^2 + 1) + 31 → z + 6 / z = -2 :=
begin
  intro h,
  let a := z.re,
  let b := z.im,
  have h1 : normSq z = a^2 + b^2 := by simp [normSq, sq],
  have h2 : normSq (z + 2) = (a + 2)^2 + b^2 := by simp [normSq, sq, add_re, add_im],
  have h3 : normSq (z^2 + 1) = (a^2 - b^2 + 1)^2 + (2 * a * b)^2 := by simp [normSq, sq, sub_re, sub_im, add_re, add_im, mul_re, mul_im],
  rw [h1, h2, h3] at h,
  simp only [sq] at h,
  ring_nf at h,
  have : 12 * (a^2 + b^2) = 2 * ((a + 2)^2 + b^2) + (a^2 - b^2 + 1)^2 + (2 * a * b)^2 + 31 := h,
  ring_nf at this,
  linarith,
  have hz : z ≠ 0 := by { intro hz, rw [hz, normSq_zero] at h, linarith },
  field_simp [hz],
  have : (a^2 + b^2) * (a^2 + b^2) = 36 := by linarith,
  have : a^2 + b^2 = 6 := by nlinarith,
  have : a = 0 := by nlinarith,
  have : b = -2 := by nlinarith,
  rw [this, this] at *,
  simp,
end