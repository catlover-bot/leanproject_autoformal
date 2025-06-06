import Mathlib.Data.Real.Basic

theorem real_number_equation (a d : ℝ) : a + 6 * d = 30 → a + 10 * d = 60 → a + 20 * d = 135 :=
begin
  intros h1 h2,
  have h3 : 4 * d = 30,
  { linarith },
  have h4 : d = 7.5,
  { linarith },
  have h5 : a = -15,
  { linarith },
  linarith,
end