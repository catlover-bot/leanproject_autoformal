import Mathlib.Data.Int.Basic
import Mathlib.Tactic

theorem imo_1992_p1
  (p q r : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ (p * q * r - 1)) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  have h₂ : ∃ k, (p - 1) * (q - 1) * (r - 1) * k = p * q * r - 1 := h₁
  obtain ⟨k, hk⟩ := h₂
  have : p * q * r = (p - 1) * (q - 1) * (r - 1) * k + 1 := by rw [hk]
  have h₃ : p ≥ 2 := by linarith
  have h₄ : q ≥ 3 := by linarith
  have h₅ : r ≥ 4 := by linarith
  interval_cases p with hp
  case h_2 =>
    interval_cases q with hq
    case h_3 =>
      interval_cases r with hr
      case h_4 =>
        have : (p, q, r) = (2, 3, 4) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 2 * 3 := by norm_num
        have : p * q * r - 1 = 23 := by norm_num
        have : ¬1 * 2 * 3 ∣ 23 := by norm_num
        contradiction
      case h_5 =>
        have : (p, q, r) = (2, 3, 5) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 2 * 4 := by norm_num
        have : p * q * r - 1 = 29 := by norm_num
        have : ¬1 * 2 * 4 ∣ 29 := by norm_num
        contradiction
      case h_6 =>
        have : (p, q, r) = (2, 3, 6) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 2 * 5 := by norm_num
        have : p * q * r - 1 = 35 := by norm_num
        have : ¬1 * 2 * 5 ∣ 35 := by norm_num
        contradiction
      case h_7 =>
        have : (p, q, r) = (2, 3, 7) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 2 * 6 := by norm_num
        have : p * q * r - 1 = 41 := by norm_num
        have : ¬1 * 2 * 6 ∣ 41 := by norm_num
        contradiction
      case h_8 =>
        have : (p, q, r) = (2, 3, 8) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 2 * 7 := by norm_num
        have : p * q * r - 1 = 47 := by norm_num
        have : ¬1 * 2 * 7 ∣ 47 := by norm_num
        contradiction
      case h_9 =>
        have : (p, q, r) = (2, 3, 9) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 2 * 8 := by norm_num
        have : p * q * r - 1 = 53 := by norm_num
        have : ¬1 * 2 * 8 ∣ 53 := by norm_num
        contradiction
    case h_4 =>
      interval_cases r with hr
      case h_5 =>
        have : (p, q, r) = (2, 4, 5) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 3 * 4 := by norm_num
        have : p * q * r - 1 = 39 := by norm_num
        have : ¬1 * 3 * 4 ∣ 39 := by norm_num
        contradiction
      case h_6 =>
        have : (p, q, r) = (2, 4, 6) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 3 * 5 := by norm_num
        have : p * q * r - 1 = 47 := by norm_num
        have : ¬1 * 3 * 5 ∣ 47 := by norm_num
        contradiction
      case h_7 =>
        have : (p, q, r) = (2, 4, 7) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 3 * 6 := by norm_num
        have : p * q * r - 1 = 55 := by norm_num
        have : ¬1 * 3 * 6 ∣ 55 := by norm_num
        contradiction
      case h_8 =>
        exact Or.inl rfl
      case h_9 =>
        have : (p, q, r) = (2, 4, 9) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 1 * 3 * 8 := by norm_num
        have : p * q * r - 1 = 71 := by norm_num
        have : ¬1 * 3 * 8 ∣ 71 := by norm_num
        contradiction
  case h_3 =>
    interval_cases q with hq
    case h_4 =>
      interval_cases r with hr
      case h_5 =>
        have : (p, q, r) = (3, 4, 5) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 3 * 4 := by norm_num
        have : p * q * r - 1 = 59 := by norm_num
        have : ¬2 * 3 * 4 ∣ 59 := by norm_num
        contradiction
      case h_6 =>
        have : (p, q, r) = (3, 4, 6) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 3 * 5 := by norm_num
        have : p * q * r - 1 = 71 := by norm_num
        have : ¬2 * 3 * 5 ∣ 71 := by norm_num
        contradiction
      case h_7 =>
        have : (p, q, r) = (3, 4, 7) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 3 * 6 := by norm_num
        have : p * q * r - 1 = 83 := by norm_num
        have : ¬2 * 3 * 6 ∣ 83 := by norm_num
        contradiction
      case h_8 =>
        have : (p, q, r) = (3, 4, 8) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 3 * 7 := by norm_num
        have : p * q * r - 1 = 95 := by norm_num
        have : ¬2 * 3 * 7 ∣ 95 := by norm_num
        contradiction
      case h_9 =>
        have : (p, q, r) = (3, 4, 9) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 3 * 8 := by norm_num
        have : p * q * r - 1 = 107 := by norm_num
        have : ¬2 * 3 * 8 ∣ 107 := by norm_num
        contradiction
    case h_5 =>
      interval_cases r with hr
      case h_6 =>
        have : (p, q, r) = (3, 5, 6) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 4 * 5 := by norm_num
        have : p * q * r - 1 = 89 := by norm_num
        have : ¬2 * 4 * 5 ∣ 89 := by norm_num
        contradiction
      case h_7 =>
        have : (p, q, r) = (3, 5, 7) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 4 * 6 := by norm_num
        have : p * q * r - 1 = 104 := by norm_num
        have : ¬2 * 4 * 6 ∣ 104 := by norm_num
        contradiction
      case h_8 =>
        have : (p, q, r) = (3, 5, 8) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 4 * 7 := by norm_num
        have : p * q * r - 1 = 119 := by norm_num
        have : ¬2 * 4 * 7 ∣ 119 := by norm_num
        contradiction
      case h_9 =>
        have : (p, q, r) = (3, 5, 9) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 2 * 4 * 8 := by norm_num
        have : p * q * r - 1 = 134 := by norm_num
        have : ¬2 * 4 * 8 ∣ 134 := by norm_num
        contradiction
      case h_15 =>
        exact Or.inr rfl
  case h_4 =>
    interval_cases q with hq
    case h_5 =>
      interval_cases r with hr
      case h_6 =>
        have : (p, q, r) = (4, 5, 6) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 5 := by norm_num
        have : p * q * r - 1 = 119 := by norm_num
        have : ¬3 * 4 * 5 ∣ 119 := by norm_num
        contradiction
      case h_7 =>
        have : (p, q, r) = (4, 5, 7) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 6 := by norm_num
        have : p * q * r - 1 = 139 := by norm_num
        have : ¬3 * 4 * 6 ∣ 139 := by norm_num
        contradiction
      case h_8 =>
        have : (p, q, r) = (4, 5, 8) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 7 := by norm_num
        have : p * q * r - 1 = 159 := by norm_num
        have : ¬3 * 4 * 7 ∣ 159 := by norm_num
        contradiction
      case h_9 =>
        have : (p, q, r) = (4, 5, 9) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 8 := by norm_num
        have : p * q * r - 1 = 179 := by norm_num
        have : ¬3 * 4 * 8 ∣ 179 := by norm_num
        contradiction
      case h_10 =>
        have : (p, q, r) = (4, 5, 10) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 9 := by norm_num
        have : p * q * r - 1 = 199 := by norm_num
        have : ¬3 * 4 * 9 ∣ 199 := by norm_num
        contradiction
      case h_11 =>
        have : (p, q, r) = (4, 5, 11) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 10 := by norm_num
        have : p * q * r - 1 = 219 := by norm_num
        have : ¬3 * 4 * 10 ∣ 219 := by norm_num
        contradiction
      case h_12 =>
        have : (p, q, r) = (4, 5, 12) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 11 := by norm_num
        have : p * q * r - 1 = 239 := by norm_num
        have : ¬3 * 4 * 11 ∣ 239 := by norm_num
        contradiction
      case h_13 =>
        have : (p, q, r) = (4, 5, 13) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 12 := by norm_num
        have : p * q * r - 1 = 259 := by norm_num
        have : ¬3 * 4 * 12 ∣ 259 := by norm_num
        contradiction
      case h_14 =>
        have : (p, q, r) = (4, 5, 14) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 13 := by norm_num
        have : p * q * r - 1 = 279 := by norm_num
        have : ¬3 * 4 * 13 ∣ 279 := by norm_num
        contradiction
      case h_15 =>
        have : (p, q, r) = (4, 5, 15) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 14 := by norm_num
        have : p * q * r - 1 = 299 := by norm_num
        have : ¬3 * 4 * 14 ∣ 299 := by norm_num
        contradiction
      case h_16 =>
        have : (p, q, r) = (4, 5, 16) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 15 := by norm_num
        have : p * q * r - 1 = 319 := by norm_num
        have : ¬3 * 4 * 15 ∣ 319 := by norm_num
        contradiction
      case h_17 =>
        have : (p, q, r) = (4, 5, 17) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 16 := by norm_num
        have : p * q * r - 1 = 339 := by norm_num
        have : ¬3 * 4 * 16 ∣ 339 := by norm_num
        contradiction
      case h_18 =>
        have : (p, q, r) = (4, 5, 18) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 17 := by norm_num
        have : p * q * r - 1 = 359 := by norm_num
        have : ¬3 * 4 * 17 ∣ 359 := by norm_num
        contradiction
      case h_19 =>
        have : (p, q, r) = (4, 5, 19) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 18 := by norm_num
        have : p * q * r - 1 = 379 := by norm_num
        have : ¬3 * 4 * 18 ∣ 379 := by norm_num
        contradiction
      case h_20 =>
        have : (p, q, r) = (4, 5, 20) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 19 := by norm_num
        have : p * q * r - 1 = 399 := by norm_num
        have : ¬3 * 4 * 19 ∣ 399 := by norm_num
        contradiction
      case h_21 =>
        have : (p, q, r) = (4, 5, 21) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 20 := by norm_num
        have : p * q * r - 1 = 419 := by norm_num
        have : ¬3 * 4 * 20 ∣ 419 := by norm_num
        contradiction
      case h_22 =>
        have : (p, q, r) = (4, 5, 22) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 21 := by norm_num
        have : p * q * r - 1 = 439 := by norm_num
        have : ¬3 * 4 * 21 ∣ 439 := by norm_num
        contradiction
      case h_23 =>
        have : (p, q, r) = (4, 5, 23) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 22 := by norm_num
        have : p * q * r - 1 = 459 := by norm_num
        have : ¬3 * 4 * 22 ∣ 459 := by norm_num
        contradiction
      case h_24 =>
        have : (p, q, r) = (4, 5, 24) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 23 := by norm_num
        have : p * q * r - 1 = 479 := by norm_num
        have : ¬3 * 4 * 23 ∣ 479 := by norm_num
        contradiction
      case h_25 =>
        have : (p, q, r) = (4, 5, 25) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 24 := by norm_num
        have : p * q * r - 1 = 499 := by norm_num
        have : ¬3 * 4 * 24 ∣ 499 := by norm_num
        contradiction
      case h_26 =>
        have : (p, q, r) = (4, 5, 26) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 25 := by norm_num
        have : p * q * r - 1 = 519 := by norm_num
        have : ¬3 * 4 * 25 ∣ 519 := by norm_num
        contradiction
      case h_27 =>
        have : (p, q, r) = (4, 5, 27) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 26 := by norm_num
        have : p * q * r - 1 = 539 := by norm_num
        have : ¬3 * 4 * 26 ∣ 539 := by norm_num
        contradiction
      case h_28 =>
        have : (p, q, r) = (4, 5, 28) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 27 := by norm_num
        have : p * q * r - 1 = 559 := by norm_num
        have : ¬3 * 4 * 27 ∣ 559 := by norm_num
        contradiction
      case h_29 =>
        have : (p, q, r) = (4, 5, 29) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 28 := by norm_num
        have : p * q * r - 1 = 579 := by norm_num
        have : ¬3 * 4 * 28 ∣ 579 := by norm_num
        contradiction
      case h_30 =>
        have : (p, q, r) = (4, 5, 30) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 29 := by norm_num
        have : p * q * r - 1 = 599 := by norm_num
        have : ¬3 * 4 * 29 ∣ 599 := by norm_num
        contradiction
      case h_31 =>
        have : (p, q, r) = (4, 5, 31) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 30 := by norm_num
        have : p * q * r - 1 = 619 := by norm_num
        have : ¬3 * 4 * 30 ∣ 619 := by norm_num
        contradiction
      case h_32 =>
        have : (p, q, r) = (4, 5, 32) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 31 := by norm_num
        have : p * q * r - 1 = 639 := by norm_num
        have : ¬3 * 4 * 31 ∣ 639 := by norm_num
        contradiction
      case h_33 =>
        have : (p, q, r) = (4, 5, 33) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 32 := by norm_num
        have : p * q * r - 1 = 659 := by norm_num
        have : ¬3 * 4 * 32 ∣ 659 := by norm_num
        contradiction
      case h_34 =>
        have : (p, q, r) = (4, 5, 34) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 33 := by norm_num
        have : p * q * r - 1 = 679 := by norm_num
        have : ¬3 * 4 * 33 ∣ 679 := by norm_num
        contradiction
      case h_35 =>
        have : (p, q, r) = (4, 5, 35) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 34 := by norm_num
        have : p * q * r - 1 = 699 := by norm_num
        have : ¬3 * 4 * 34 ∣ 699 := by norm_num
        contradiction
      case h_36 =>
        have : (p, q, r) = (4, 5, 36) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 35 := by norm_num
        have : p * q * r - 1 = 719 := by norm_num
        have : ¬3 * 4 * 35 ∣ 719 := by norm_num
        contradiction
      case h_37 =>
        have : (p, q, r) = (4, 5, 37) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 36 := by norm_num
        have : p * q * r - 1 = 739 := by norm_num
        have : ¬3 * 4 * 36 ∣ 739 := by norm_num
        contradiction
      case h_38 =>
        have : (p, q, r) = (4, 5, 38) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 37 := by norm_num
        have : p * q * r - 1 = 759 := by norm_num
        have : ¬3 * 4 * 37 ∣ 759 := by norm_num
        contradiction
      case h_39 =>
        have : (p, q, r) = (4, 5, 39) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 38 := by norm_num
        have : p * q * r - 1 = 779 := by norm_num
        have : ¬3 * 4 * 38 ∣ 779 := by norm_num
        contradiction
      case h_40 =>
        have : (p, q, r) = (4, 5, 40) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 39 := by norm_num
        have : p * q * r - 1 = 799 := by norm_num
        have : ¬3 * 4 * 39 ∣ 799 := by norm_num
        contradiction
      case h_41 =>
        have : (p, q, r) = (4, 5, 41) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 40 := by norm_num
        have : p * q * r - 1 = 819 := by norm_num
        have : ¬3 * 4 * 40 ∣ 819 := by norm_num
        contradiction
      case h_42 =>
        have : (p, q, r) = (4, 5, 42) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 41 := by norm_num
        have : p * q * r - 1 = 839 := by norm_num
        have : ¬3 * 4 * 41 ∣ 839 := by norm_num
        contradiction
      case h_43 =>
        have : (p, q, r) = (4, 5, 43) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 42 := by norm_num
        have : p * q * r - 1 = 859 := by norm_num
        have : ¬3 * 4 * 42 ∣ 859 := by norm_num
        contradiction
      case h_44 =>
        have : (p, q, r) = (4, 5, 44) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 43 := by norm_num
        have : p * q * r - 1 = 879 := by norm_num
        have : ¬3 * 4 * 43 ∣ 879 := by norm_num
        contradiction
      case h_45 =>
        have : (p, q, r) = (4, 5, 45) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 44 := by norm_num
        have : p * q * r - 1 = 899 := by norm_num
        have : ¬3 * 4 * 44 ∣ 899 := by norm_num
        contradiction
      case h_46 =>
        have : (p, q, r) = (4, 5, 46) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 45 := by norm_num
        have : p * q * r - 1 = 919 := by norm_num
        have : ¬3 * 4 * 45 ∣ 919 := by norm_num
        contradiction
      case h_47 =>
        have : (p, q, r) = (4, 5, 47) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 46 := by norm_num
        have : p * q * r - 1 = 939 := by norm_num
        have : ¬3 * 4 * 46 ∣ 939 := by norm_num
        contradiction
      case h_48 =>
        have : (p, q, r) = (4, 5, 48) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 47 := by norm_num
        have : p * q * r - 1 = 959 := by norm_num
        have : ¬3 * 4 * 47 ∣ 959 := by norm_num
        contradiction
      case h_49 =>
        have : (p, q, r) = (4, 5, 49) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 48 := by norm_num
        have : p * q * r - 1 = 979 := by norm_num
        have : ¬3 * 4 * 48 ∣ 979 := by norm_num
        contradiction
      case h_50 =>
        have : (p, q, r) = (4, 5, 50) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 49 := by norm_num
        have : p * q * r - 1 = 999 := by norm_num
        have : ¬3 * 4 * 49 ∣ 999 := by norm_num
        contradiction
      case h_51 =>
        have : (p, q, r) = (4, 5, 51) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 50 := by norm_num
        have : p * q * r - 1 = 1019 := by norm_num
        have : ¬3 * 4 * 50 ∣ 1019 := by norm_num
        contradiction
      case h_52 =>
        have : (p, q, r) = (4, 5, 52) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 51 := by norm_num
        have : p * q * r - 1 = 1039 := by norm_num
        have : ¬3 * 4 * 51 ∣ 1039 := by norm_num
        contradiction
      case h_53 =>
        have : (p, q, r) = (4, 5, 53) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 52 := by norm_num
        have : p * q * r - 1 = 1059 := by norm_num
        have : ¬3 * 4 * 52 ∣ 1059 := by norm_num
        contradiction
      case h_54 =>
        have : (p, q, r) = (4, 5, 54) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 53 := by norm_num
        have : p * q * r - 1 = 1079 := by norm_num
        have : ¬3 * 4 * 53 ∣ 1079 := by norm_num
        contradiction
      case h_55 =>
        have : (p, q, r) = (4, 5, 55) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 54 := by norm_num
        have : p * q * r - 1 = 1099 := by norm_num
        have : ¬3 * 4 * 54 ∣ 1099 := by norm_num
        contradiction
      case h_56 =>
        have : (p, q, r) = (4, 5, 56) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 55 := by norm_num
        have : p * q * r - 1 = 1119 := by norm_num
        have : ¬3 * 4 * 55 ∣ 1119 := by norm_num
        contradiction
      case h_57 =>
        have : (p, q, r) = (4, 5, 57) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 56 := by norm_num
        have : p * q * r - 1 = 1139 := by norm_num
        have : ¬3 * 4 * 56 ∣ 1139 := by norm_num
        contradiction
      case h_58 =>
        have : (p, q, r) = (4, 5, 58) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 57 := by norm_num
        have : p * q * r - 1 = 1159 := by norm_num
        have : ¬3 * 4 * 57 ∣ 1159 := by norm_num
        contradiction
      case h_59 =>
        have : (p, q, r) = (4, 5, 59) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 58 := by norm_num
        have : p * q * r - 1 = 1179 := by norm_num
        have : ¬3 * 4 * 58 ∣ 1179 := by norm_num
        contradiction
      case h_60 =>
        have : (p, q, r) = (4, 5, 60) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 59 := by norm_num
        have : p * q * r - 1 = 1199 := by norm_num
        have : ¬3 * 4 * 59 ∣ 1199 := by norm_num
        contradiction
      case h_61 =>
        have : (p, q, r) = (4, 5, 61) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 60 := by norm_num
        have : p * q * r - 1 = 1219 := by norm_num
        have : ¬3 * 4 * 60 ∣ 1219 := by norm_num
        contradiction
      case h_62 =>
        have : (p, q, r) = (4, 5, 62) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 61 := by norm_num
        have : p * q * r - 1 = 1239 := by norm_num
        have : ¬3 * 4 * 61 ∣ 1239 := by norm_num
        contradiction
      case h_63 =>
        have : (p, q, r) = (4, 5, 63) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 62 := by norm_num
        have : p * q * r - 1 = 1259 := by norm_num
        have : ¬3 * 4 * 62 ∣ 1259 := by norm_num
        contradiction
      case h_64 =>
        have : (p, q, r) = (4, 5, 64) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 63 := by norm_num
        have : p * q * r - 1 = 1279 := by norm_num
        have : ¬3 * 4 * 63 ∣ 1279 := by norm_num
        contradiction
      case h_65 =>
        have : (p, q, r) = (4, 5, 65) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 64 := by norm_num
        have : p * q * r - 1 = 1299 := by norm_num
        have : ¬3 * 4 * 64 ∣ 1299 := by norm_num
        contradiction
      case h_66 =>
        have : (p, q, r) = (4, 5, 66) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 65 := by norm_num
        have : p * q * r - 1 = 1319 := by norm_num
        have : ¬3 * 4 * 65 ∣ 1319 := by norm_num
        contradiction
      case h_67 =>
        have : (p, q, r) = (4, 5, 67) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 66 := by norm_num
        have : p * q * r - 1 = 1339 := by norm_num
        have : ¬3 * 4 * 66 ∣ 1339 := by norm_num
        contradiction
      case h_68 =>
        have : (p, q, r) = (4, 5, 68) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 67 := by norm_num
        have : p * q * r - 1 = 1359 := by norm_num
        have : ¬3 * 4 * 67 ∣ 1359 := by norm_num
        contradiction
      case h_69 =>
        have : (p, q, r) = (4, 5, 69) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 68 := by norm_num
        have : p * q * r - 1 = 1379 := by norm_num
        have : ¬3 * 4 * 68 ∣ 1379 := by norm_num
        contradiction
      case h_70 =>
        have : (p, q, r) = (4, 5, 70) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 69 := by norm_num
        have : p * q * r - 1 = 1399 := by norm_num
        have : ¬3 * 4 * 69 ∣ 1399 := by norm_num
        contradiction
      case h_71 =>
        have : (p, q, r) = (4, 5, 71) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 70 := by norm_num
        have : p * q * r - 1 = 1419 := by norm_num
        have : ¬3 * 4 * 70 ∣ 1419 := by norm_num
        contradiction
      case h_72 =>
        have : (p, q, r) = (4, 5, 72) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 71 := by norm_num
        have : p * q * r - 1 = 1439 := by norm_num
        have : ¬3 * 4 * 71 ∣ 1439 := by norm_num
        contradiction
      case h_73 =>
        have : (p, q, r) = (4, 5, 73) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 72 := by norm_num
        have : p * q * r - 1 = 1459 := by norm_num
        have : ¬3 * 4 * 72 ∣ 1459 := by norm_num
        contradiction
      case h_74 =>
        have : (p, q, r) = (4, 5, 74) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 73 := by norm_num
        have : p * q * r - 1 = 1479 := by norm_num
        have : ¬3 * 4 * 73 ∣ 1479 := by norm_num
        contradiction
      case h_75 =>
        have : (p, q, r) = (4, 5, 75) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 74 := by norm_num
        have : p * q * r - 1 = 1499 := by norm_num
        have : ¬3 * 4 * 74 ∣ 1499 := by norm_num
        contradiction
      case h_76 =>
        have : (p, q, r) = (4, 5, 76) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 75 := by norm_num
        have : p * q * r - 1 = 1519 := by norm_num
        have : ¬3 * 4 * 75 ∣ 1519 := by norm_num
        contradiction
      case h_77 =>
        have : (p, q, r) = (4, 5, 77) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 76 := by norm_num
        have : p * q * r - 1 = 1539 := by norm_num
        have : ¬3 * 4 * 76 ∣ 1539 := by norm_num
        contradiction
      case h_78 =>
        have : (p, q, r) = (4, 5, 78) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 77 := by norm_num
        have : p * q * r - 1 = 1559 := by norm_num
        have : ¬3 * 4 * 77 ∣ 1559 := by norm_num
        contradiction
      case h_79 =>
        have : (p, q, r) = (4, 5, 79) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 78 := by norm_num
        have : p * q * r - 1 = 1579 := by norm_num
        have : ¬3 * 4 * 78 ∣ 1579 := by norm_num
        contradiction
      case h_80 =>
        have : (p, q, r) = (4, 5, 80) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 79 := by norm_num
        have : p * q * r - 1 = 1599 := by norm_num
        have : ¬3 * 4 * 79 ∣ 1599 := by norm_num
        contradiction
      case h_81 =>
        have : (p, q, r) = (4, 5, 81) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 80 := by norm_num
        have : p * q * r - 1 = 1619 := by norm_num
        have : ¬3 * 4 * 80 ∣ 1619 := by norm_num
        contradiction
      case h_82 =>
        have : (p, q, r) = (4, 5, 82) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 81 := by norm_num
        have : p * q * r - 1 = 1639 := by norm_num
        have : ¬3 * 4 * 81 ∣ 1639 := by norm_num
        contradiction
      case h_83 =>
        have : (p, q, r) = (4, 5, 83) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 82 := by norm_num
        have : p * q * r - 1 = 1659 := by norm_num
        have : ¬3 * 4 * 82 ∣ 1659 := by norm_num
        contradiction
      case h_84 =>
        have : (p, q, r) = (4, 5, 84) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 83 := by norm_num
        have : p * q * r - 1 = 1679 := by norm_num
        have : ¬3 * 4 * 83 ∣ 1679 := by norm_num
        contradiction
      case h_85 =>
        have : (p, q, r) = (4, 5, 85) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 84 := by norm_num
        have : p * q * r - 1 = 1699 := by norm_num
        have : ¬3 * 4 * 84 ∣ 1699 := by norm_num
        contradiction
      case h_86 =>
        have : (p, q, r) = (4, 5, 86) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 85 := by norm_num
        have : p * q * r - 1 = 1719 := by norm_num
        have : ¬3 * 4 * 85 ∣ 1719 := by norm_num
        contradiction
      case h_87 =>
        have : (p, q, r) = (4, 5, 87) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 86 := by norm_num
        have : p * q * r - 1 = 1739 := by norm_num
        have : ¬3 * 4 * 86 ∣ 1739 := by norm_num
        contradiction
      case h_88 =>
        have : (p, q, r) = (4, 5, 88) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 87 := by norm_num
        have : p * q * r - 1 = 1759 := by norm_num
        have : ¬3 * 4 * 87 ∣ 1759 := by norm_num
        contradiction
      case h_89 =>
        have : (p, q, r) = (4, 5, 89) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 88 := by norm_num
        have : p * q * r - 1 = 1779 := by norm_num
        have : ¬3 * 4 * 88 ∣ 1779 := by norm_num
        contradiction
      case h_90 =>
        have : (p, q, r) = (4, 5, 90) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 89 := by norm_num
        have : p * q * r - 1 = 1799 := by norm_num
        have : ¬3 * 4 * 89 ∣ 1799 := by norm_num
        contradiction
      case h_91 =>
        have : (p, q, r) = (4, 5, 91) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 90 := by norm_num
        have : p * q * r - 1 = 1819 := by norm_num
        have : ¬3 * 4 * 90 ∣ 1819 := by norm_num
        contradiction
      case h_92 =>
        have : (p, q, r) = (4, 5, 92) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 91 := by norm_num
        have : p * q * r - 1 = 1839 := by norm_num
        have : ¬3 * 4 * 91 ∣ 1839 := by norm_num
        contradiction
      case h_93 =>
        have : (p, q, r) = (4, 5, 93) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 92 := by norm_num
        have : p * q * r - 1 = 1859 := by norm_num
        have : ¬3 * 4 * 92 ∣ 1859 := by norm_num
        contradiction
      case h_94 =>
        have : (p, q, r) = (4, 5, 94) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 93 := by norm_num
        have : p * q * r - 1 = 1879 := by norm_num
        have : ¬3 * 4 * 93 ∣ 1879 := by norm_num
        contradiction
      case h_95 =>
        have : (p, q, r) = (4, 5, 95) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 94 := by norm_num
        have : p * q * r - 1 = 1899 := by norm_num
        have : ¬3 * 4 * 94 ∣ 1899 := by norm_num
        contradiction
      case h_96 =>
        have : (p, q, r) = (4, 5, 96) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 95 := by norm_num
        have : p * q * r - 1 = 1919 := by norm_num
        have : ¬3 * 4 * 95 ∣ 1919 := by norm_num
        contradiction
      case h_97 =>
        have : (p, q, r) = (4, 5, 97) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 96 := by norm_num
        have : p * q * r - 1 = 1939 := by norm_num
        have : ¬3 * 4 * 96 ∣ 1939 := by norm_num
        contradiction
      case h_98 =>
        have : (p, q, r) = (4, 5, 98) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 97 := by norm_num
        have : p * q * r - 1 = 1959 := by norm_num
        have : ¬3 * 4 * 97 ∣ 1959 := by norm_num
        contradiction
      case h_99 =>
        have : (p, q, r) = (4, 5, 99) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 98 := by norm_num
        have : p * q * r - 1 = 1979 := by norm_num
        have : ¬3 * 4 * 98 ∣ 1979 := by norm_num
        contradiction
      case h_100 =>
        have : (p, q, r) = (4, 5, 100) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 99 := by norm_num
        have : p * q * r - 1 = 1999 := by norm_num
        have : ¬3 * 4 * 99 ∣ 1999 := by norm_num
        contradiction
      case h_101 =>
        have : (p, q, r) = (4, 5, 101) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 100 := by norm_num
        have : p * q * r - 1 = 2019 := by norm_num
        have : ¬3 * 4 * 100 ∣ 2019 := by norm_num
        contradiction
      case h_102 =>
        have : (p, q, r) = (4, 5, 102) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 101 := by norm_num
        have : p * q * r - 1 = 2039 := by norm_num
        have : ¬3 * 4 * 101 ∣ 2039 := by norm_num
        contradiction
      case h_103 =>
        have : (p, q, r) = (4, 5, 103) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 102 := by norm_num
        have : p * q * r - 1 = 2059 := by norm_num
        have : ¬3 * 4 * 102 ∣ 2059 := by norm_num
        contradiction
      case h_104 =>
        have : (p, q, r) = (4, 5, 104) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 103 := by norm_num
        have : p * q * r - 1 = 2079 := by norm_num
        have : ¬3 * 4 * 103 ∣ 2079 := by norm_num
        contradiction
      case h_105 =>
        have : (p, q, r) = (4, 5, 105) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 104 := by norm_num
        have : p * q * r - 1 = 2099 := by norm_num
        have : ¬3 * 4 * 104 ∣ 2099 := by norm_num
        contradiction
      case h_106 =>
        have : (p, q, r) = (4, 5, 106) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 105 := by norm_num
        have : p * q * r - 1 = 2119 := by norm_num
        have : ¬3 * 4 * 105 ∣ 2119 := by norm_num
        contradiction
      case h_107 =>
        have : (p, q, r) = (4, 5, 107) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 106 := by norm_num
        have : p * q * r - 1 = 2139 := by norm_num
        have : ¬3 * 4 * 106 ∣ 2139 := by norm_num
        contradiction
      case h_108 =>
        have : (p, q, r) = (4, 5, 108) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 107 := by norm_num
        have : p * q * r - 1 = 2159 := by norm_num
        have : ¬3 * 4 * 107 ∣ 2159 := by norm_num
        contradiction
      case h_109 =>
        have : (p, q, r) = (4, 5, 109) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 108 := by norm_num
        have : p * q * r - 1 = 2179 := by norm_num
        have : ¬3 * 4 * 108 ∣ 2179 := by norm_num
        contradiction
      case h_110 =>
        have : (p, q, r) = (4, 5, 110) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 109 := by norm_num
        have : p * q * r - 1 = 2199 := by norm_num
        have : ¬3 * 4 * 109 ∣ 2199 := by norm_num
        contradiction
      case h_111 =>
        have : (p, q, r) = (4, 5, 111) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 110 := by norm_num
        have : p * q * r - 1 = 2219 := by norm_num
        have : ¬3 * 4 * 110 ∣ 2219 := by norm_num
        contradiction
      case h_112 =>
        have : (p, q, r) = (4, 5, 112) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 111 := by norm_num
        have : p * q * r - 1 = 2239 := by norm_num
        have : ¬3 * 4 * 111 ∣ 2239 := by norm_num
        contradiction
      case h_113 =>
        have : (p, q, r) = (4, 5, 113) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 112 := by norm_num
        have : p * q * r - 1 = 2259 := by norm_num
        have : ¬3 * 4 * 112 ∣ 2259 := by norm_num
        contradiction
      case h_114 =>
        have : (p, q, r) = (4, 5, 114) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 113 := by norm_num
        have : p * q * r - 1 = 2279 := by norm_num
        have : ¬3 * 4 * 113 ∣ 2279 := by norm_num
        contradiction
      case h_115 =>
        have : (p, q, r) = (4, 5, 115) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 114 := by norm_num
        have : p * q * r - 1 = 2299 := by norm_num
        have : ¬3 * 4 * 114 ∣ 2299 := by norm_num
        contradiction
      case h_116 =>
        have : (p, q, r) = (4, 5, 116) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 115 := by norm_num
        have : p * q * r - 1 = 2319 := by norm_num
        have : ¬3 * 4 * 115 ∣ 2319 := by norm_num
        contradiction
      case h_117 =>
        have : (p, q, r) = (4, 5, 117) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 116 := by norm_num
        have : p * q * r - 1 = 2339 := by norm_num
        have : ¬3 * 4 * 116 ∣ 2339 := by norm_num
        contradiction
      case h_118 =>
        have : (p, q, r) = (4, 5, 118) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 117 := by norm_num
        have : p * q * r - 1 = 2359 := by norm_num
        have : ¬3 * 4 * 117 ∣ 2359 := by norm_num
        contradiction
      case h_119 =>
        have : (p, q, r) = (4, 5, 119) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 118 := by norm_num
        have : p * q * r - 1 = 2379 := by norm_num
        have : ¬3 * 4 * 118 ∣ 2379 := by norm_num
        contradiction
      case h_120 =>
        have : (p, q, r) = (4, 5, 120) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 119 := by norm_num
        have : p * q * r - 1 = 2399 := by norm_num
        have : ¬3 * 4 * 119 ∣ 2399 := by norm_num
        contradiction
      case h_121 =>
        have : (p, q, r) = (4, 5, 121) := by simp [hp, hq, hr]
        have : (p - 1) * (q - 1) * (r - 1) = 3 * 4 * 120 := by norm_num
        have : p * q * r - 1 = 2419 := by norm_num
        have : ¬3 * 4 * 120 ∣ 2419 := by norm_num
        contradiction
      case h_122 =>
        have : (p, q, r) = (4, 5, 122)