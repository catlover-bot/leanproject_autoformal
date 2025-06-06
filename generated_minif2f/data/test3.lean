import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

theorem aime_1983_p1
  (x y z w : ℕ)
  (ht : 1 < x ∧ 1 < y ∧ 1 < z)
  (hw : 0 ≤ w)
  (h0 : real.log w / real.log x = 24)
  (h1 : real.log w / real.log y = 40)
  (h2 : real.log w / real.log (x * y * z) = 12) :
  real.log w / real.log z = 60 :=
begin
  have hx : real.log x ≠ 0 := by linarith [real.log_pos ht.1],
  have hy : real.log y ≠ 0 := by linarith [real.log_pos ht.2.1],
  have hz : real.log z ≠ 0 := by linarith [real.log_pos ht.2.2],
  have hxyz : real.log (x * y * z) = real.log x + real.log y + real.log z := real.log_mul (x * y) z ▸ real.log_mul x y,
  have h3 : real.log w = 24 * real.log x := (eq_div_iff hx).mp h0,
  have h4 : real.log w = 40 * real.log y := (eq_div_iff hy).mp h1,
  have h5 : real.log w = 12 * (real.log x + real.log y + real.log z) := (eq_div_iff (by linarith [real.log_pos (mul_pos (mul_pos ht.1 ht.2.1) ht.2.2)])).mp h2,
  have h6 : 24 * real.log x = 40 * real.log y := by rw [h3, h4],
  have h7 : 24 * real.log x = 12 * (real.log x + real.log y + real.log z) := by rw [h3, h5],
  have h8 : 40 * real.log y = 12 * (real.log x + real.log y + real.log z) := by rw [h4, h5],
  have h9 : 24 * real.log x = 12 * real.log x + 12 * real.log y + 12 * real.log z := by rw [h7, hxyz],
  have h10 : 40 * real.log y = 12 * real.log x + 12 * real.log y + 12 * real.log z := by rw [h8, hxyz],
  have h11 : 12 * real.log x + 12 * real.log y + 12 * real.log z = 12 * real.log x + 12 * real.log y + 12 * real.log z := by refl,
  have h12 : 12 * real.log z = 720 := by linarith [h9, h10, h11],
  have h13 : real.log z = 60 := by linarith [h12],
  exact (eq_div_iff hz).mpr (by rw [h5, h13, mul_comm, mul_div_cancel_left _ (by norm_num)]),
end