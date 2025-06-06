import Mathlib.Data.Real.Basic

theorem solve_system (x y z : ℝ) :
  (3 * x + y = 17) → (5 * y + z = 14) → (3 * x + 5 * z = 41) → (x + y + z = 12) :=
begin
  intros h1 h2 h3,
  have h4 : 3 * x + 5 * (14 - 5 * y) = 41, { rw [←h2], ring },
  have h5 : 3 * x + 70 - 25 * y = 41, { linarith },
  have h6 : 3 * x - 25 * y = -29, { linarith },
  have h7 : 3 * x + y = 17, { exact h1 },
  have h8 : 26 * y = 46, { linarith },
  have h9 : y = 46 / 26, { linarith },
  have h10 : y = 23 / 13, { norm_num at h9, exact h9 },
  have h11 : 3 * x + 23 / 13 = 17, { rw h10 at h7, exact h7 },
  have h12 : 3 * x = 17 - 23 / 13, { linarith },
  have h13 : 3 * x = 198 / 13, { norm_num at h12, exact h12 },
  have h14 : x = 66 / 13, { linarith },
  have h15 : 5 * (23 / 13) + z = 14, { rw h10 at h2, exact h2 },
  have h16 : 115 / 13 + z = 14, { norm_num at h15, exact h15 },
  have h17 : z = 14 - 115 / 13, { linarith },
  have h18 : z = 67 / 13, { norm_num at h17, exact h17 },
  have h19 : x + y + z = 66 / 13 + 23 / 13 + 67 / 13, { rw [h14, h10, h18] },
  have h20 : x + y + z = (66 + 23 + 67) / 13, { ring },
  have h21 : x + y + z = 156 / 13, { norm_num at h20, exact h20 },
  norm_num at h21,
  exact h21,
end