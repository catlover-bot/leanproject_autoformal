import Mathlib.Data.Real.Basic

open Real

theorem product_of_exponents (a b c d : ℝ) 
  (h1 : 4^a = 5) (h2 : 5^b = 6) (h3 : 6^c = 7) (h4 : 7^d = 8) : 
  a * b * c * d = 3 / 2 :=
begin
  -- Express each variable in logarithmic form
  have ha : a = log 5 / log 4, from (log_eq_of_pow_eq h1).symm,
  have hb : b = log 6 / log 5, from (log_eq_of_pow_eq h2).symm,
  have hc : c = log 7 / log 6, from (log_eq_of_pow_eq h3).symm,
  have hd : d = log 8 / log 7, from (log_eq_of_pow_eq h4).symm,

  -- Multiply the expressions for a, b, c, and d
  calc a * b * c * d 
      = (log 5 / log 4) * (log 6 / log 5) * (log 7 / log 6) * (log 8 / log 7) : by rw [ha, hb, hc, hd]
  ... = (log 8 / log 4) : by { field_simp, ring }
  ... = (3 * log 2) / (2 * log 2) : by rw [log_div_log, log_div_log]
  ... = 3 / 2 : by { field_simp [log_pos (by norm_num : (2 : ℝ) > 0)], ring }
end