import data.finset
import data.nat.parity
import algebra.big_operators

open finset
open_locale big_operators

theorem product_of_first_six_odds_mod_10 : (∏ k in range 6, (2 * k + 1)) % 10 = 5 :=
begin
  have h : ∏ k in range 6, (2 * k + 1) = 1 * 3 * 5 * 7 * 9 * 11,
  { simp },
  rw h,
  norm_num,
end