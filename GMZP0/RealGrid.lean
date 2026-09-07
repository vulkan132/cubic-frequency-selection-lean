import GMZP0.PhaseScale

/-! Exact real rounding estimates used in the finite candidate grids. -/

noncomputable section
namespace GMZP0

/-- Rounding to a grid of spacing s loses at most s/2. -/
theorem real_grid_rounding (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ∃ l : ℤ, |t - (l : ℝ) * s| ≤ s / 2 ∧ |(l : ℝ)| ≤ |t| / s + 1 / 2 := by
  let l : ℤ := round (t / s)
  have hr : |t / s - (l : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have heq : t - (l : ℝ) * s = (t / s - (l : ℝ)) * s := by
    field_simp
  refine ⟨l, ?_, ?_⟩
  · rw [heq, abs_mul, abs_of_pos hs]
    have h := mul_le_mul_of_nonneg_right hr hs.le
    linarith
  · have htri := abs_sub (t / s) (t / s - (l : ℝ))
    simp only [sub_sub_cancel] at htri
    rw [abs_div, abs_of_pos hs] at htri
    linarith

/-- Rounding at the natural N⁻³ spacing, with no omitted remainder interval. -/
theorem cubic_scale_grid_rounding {N : ℕ} (hN : 0 < N) (b : ℝ) (hb : 0 < b) (t : ℝ) :
    ∃ l : ℤ, |t - (l : ℝ) * b / (N : ℝ) ^ 3| ≤ b / (2 * (N : ℝ) ^ 3) ∧
      |(l : ℝ)| ≤ |t| * (N : ℝ) ^ 3 / b + 1 / 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨l, herr, hbound⟩ := real_grid_rounding (b / (N : ℝ) ^ 3) (by positivity) t
  refine ⟨l, ?_, ?_⟩
  · simpa only [mul_div_assoc, div_div, mul_comm (2 : ℝ)] using herr
  · convert hbound using 1; field_simp

end GMZP0
