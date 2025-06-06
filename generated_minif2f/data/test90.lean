import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MyNamespace

theorem problem_statement (r n : ℕ) (hr : r = 1342 % 13) (hn : 0 < n) (hdvd : 1342 ∣ n) (hmod : n % 13 < r) : 6710 ≤ n := by
  have h1342mod : 1342 % 13 = 3 := by norm_num
  rw [←h1342mod] at hr
  rw [hr] at hmod
  have h1342pos : 0 < 1342 := by norm_num
  have h13pos : 0 < 13 := by norm_num
  have h1342div : 1342 = 13 * 103 + 3 := by norm_num
  have h13dvd : 13 ∣ 1342 := by
    use 103
    exact h1342div
  have h13dvdn : 13 ∣ n := Nat.dvd_trans h13dvd hdvd
  have h13mod : n % 13 = 0 := Nat.mod_eq_zero_of_dvd h13dvdn
  linarith

end MyNamespace