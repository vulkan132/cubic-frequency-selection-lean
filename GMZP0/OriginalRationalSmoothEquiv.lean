import GMZP0.RationalCoordinateLieGroup

/-! Actual smoothness of both directions of a global original-group
equivalence follows from its proved literal rational coordinate arrays. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0

/-- Both directions are smooth on the original manifold, with its given
topology and global chart. This applies to the actual time-one inverse. -/
theorem original_rational_equiv_smooth
    {G sigma : Type*} [TopologicalSpace G] [Nonempty G] [Fintype sigma]
    (coord : G ≃ₜ (sigma → ℝ)) (logCoord : G ≃ (sigma → ℝ))
    (S T : sigma → MvPolynomial sigma ℚ)
    (hS : ∀ x i, coord (logCoord.symm x) i = MvPolynomial.aeval x (S i))
    (hT : ∀ a i, logCoord a i = MvPolynomial.aeval (coord a) (T i)) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    ContMDiff 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) ∞ logCoord.symm ∧
      ContMDiff 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) ∞ logCoord := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  have hpoly (P : sigma → MvPolynomial sigma ℚ) :
      ContDiff ℝ ∞ (fun x : sigma → ℝ => fun i => MvPolynomial.aeval x (P i)) := by
    apply contDiff_pi.mpr
    intro i
    exact rational_coordinate_polynomial_contDiff ∞ (P i) id (fun j => contDiff_apply ℝ ℝ j)
  constructor
  · apply ContMDiff.of_comp_isOpenEmbedding coord.isOpenEmbedding
    have heq : coord ∘ logCoord.symm =
        (fun x : sigma → ℝ => fun i => MvPolynomial.aeval x (S i)) := by
      funext x i
      exact hS x i
    rw [heq]
    exact (hpoly S).contMDiff
  · have hc : ContMDiff 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) ∞ coord :=
      contMDiff_isOpenEmbedding coord.isOpenEmbedding
    have heq : (logCoord : G → sigma → ℝ) =
        (fun x : sigma → ℝ => fun i => MvPolynomial.aeval x (T i)) ∘ coord := by
      funext a i
      exact hT a i
    rw [heq]
    exact (hpoly T).comp_contMDiff hc

end GMZP0
