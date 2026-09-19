import GMZP0.PolynomialGroupRightMetric

/-! The constructed bounded metric must not be advertised as globally
bi-Lipschitz to unbounded original coordinates. -/
noncomputable section
namespace GMZP0

/-- Even for the additive real group, no finite global constant bounds
the original unbounded coordinate by the constructed bounded distance. -/
theorem right_regular_real_global_comparison_obstruction :
    ¬ ∃ L : ℝ, 0 ≤ L ∧ ∀ x : Multiplicative ℝ,
      |x.toAdd| ≤ L * dist (rightRegularPeak x) (rightRegularPeak (1 : Multiplicative ℝ)) := by
  rintro ⟨L, hL, hbound⟩
  have h := hbound (Multiplicative.ofAdd (L + 1))
  have hd := right_regular_peak_dist_le_one (Multiplicative.ofAdd (L + 1)) (1 : Multiplicative ℝ)
  change |L + 1| ≤ _ at h
  rw [abs_of_nonneg (by linarith)] at h
  have hm := mul_le_mul_of_nonneg_left hd hL
  linarith

end GMZP0
