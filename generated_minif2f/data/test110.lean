import Mathlib.Data.Real.Basic

open Real

theorem abcdeq : ∀ (a b c d : ℝ), (4^a = 5) → (5^b = 6) → (6^c = 7) → (7^d = 8) → a * b * c * d = 3 / 2 :=
begin
  intros a b c d ha hb hc hd,
  have ha' : a = log 5 / log 4 := by rw [← log_eq_log (pow_pos (by norm_num) a) (by norm_num), log_pow, ha],
  have hb' : b = log 6 / log 5 := by rw [← log_eq_log (pow_pos (by norm_num) b) (by norm_num), log_pow, hb],
  have hc' : c = log 7 / log 6 := by rw [← log_eq_log (pow_pos (by norm_num) c) (by norm_num), log_pow, hc],
  have hd' : d = log 8 / log 7 := by rw [← log_eq_log (pow_pos (by norm_num) d) (by norm_num), log_pow, hd],
  rw [ha', hb', hc', hd'],
  field_simp [log_ne_zero, ne_of_gt (log_pos (by norm_num : 1 < 4)), ne_of_gt (log_pos (by norm_num : 1 < 5)), ne_of_gt (log_pos (by norm_num : 1 < 6)), ne_of_gt (log_pos (by norm_num : 1 < 7))],
  have : log 8 = 3 * log 2 := by rw [log_eq_log (by norm_num : 8 = 2^3), log_pow, log_two_eq_log_two],
  rw this,
  ring,
end