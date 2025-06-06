import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

theorem aime_1983_p1
  (x y z w : ℕ)
  (ht : 1 < x ∧ 1 < y ∧ 1 < z)
  (hw : 0 ≤ w)
  (h0 : Real.log w / Real.log x = 24)
  (h1 : Real.log w / Real.log y = 40)
  (h2 : Real.log w / Real.log (x * y * z) = 12) :
  Real.log w / Real.log z = 60 :=
begin
  have hx : 0 < Real.log x, from Real.log_pos (by linarith) (by norm_num),
  have hy : 0 < Real.log y, from Real.log_pos (by linarith) (by norm_num),
  have hz : 0 < Real.log z, from Real.log_pos (by linarith) (by norm_num),
  have hxy : 0 < Real.log (x * y * z), from Real.log_pos (by linarith) (by norm_num),

  have hwx : Real.log w = 24 * Real.log x, from (eq_div_iff hx.ne').mp h0,
  have hwy : Real.log w = 40 * Real.log y, from (eq_div_iff hy.ne').mp h1,
  have hwxyz : Real.log w = 12 * Real.log (x * y * z), from (eq_div_iff hxy.ne').mp h2,

  have hxyz : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z,
  { rw Real.log_mul (by linarith) (by linarith),
    rw Real.log_mul (by linarith) (by linarith),
    ring },

  rw hxyz at hwxyz,
  rw [hwx, hwy] at hwxyz,

  have : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z),
  { rw hwxyz, exact hwx.symm },
  have : 40 * Real.log y = 12 * (Real.log x + Real.log y + Real.log z),
  { rw hwxyz, exact hwy.symm },

  have hlogx : 24 * Real.log x = 12 * Real.log x + 12 * Real.log y + 12 * Real.log z,
  { rw this },
  have hlogy : 40 * Real.log y = 12 * Real.log x + 12 * Real.log y + 12 * Real.log z,
  { rw this },

  have : 12 * Real.log z = 24 * Real.log x - 12 * Real.log x,
  { linarith },
  have : 12 * Real.log z = 40 * Real.log y - 12 * Real.log y,
  { linarith },

  have : 12 * Real.log z = 12 * Real.log x,
  { linarith },
  have : 12 * Real.log z = 28 * Real.log y,
  { linarith },

  have : Real.log z = 2 * Real.log x,
  { linarith },
  have : Real.log z = (28 / 12) * Real.log y,
  { linarith },

  have : Real.log z = 2 * Real.log x,
  { linarith },
  have : Real.log z = (7 / 3) * Real.log y,
  { linarith },

  have : Real.log w = 60 * Real.log z,
  { rw [this, hwx], ring },

  exact (eq_div_iff hz.ne').mpr this,
end