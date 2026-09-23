import GMZP0.OriginalChartDifferential
import GMZP0.RationalCoordinateDifferential

/-! The derivative of an original coordinate curve is its actual
manifold tangent. This bridges the previously constructed subgroups to
the tangent-space convention used by the actual Lie algebra. -/
noncomputable section
open scoped Manifold
namespace GMZP0
variable {G E : Type*} [TopologicalSpace G] [Nonempty G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- A curve's actual manifold derivative is equivalent to the derivative
of its original coordinates, with the same continuous linear map. -/
theorem original_curve_has_mfderiv_iff (coord : G ≃ₜ E) (gamma : ℝ → G)
    (t : ℝ) (D : ℝ →L[ℝ] E) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma t D ↔ HasFDerivAt (coord ∘ gamma) D t := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  have hw : writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) t gamma = coord ∘ gamma := by
    simp only [writtenInExtChartAt, mfld_simps]
  constructor
  · intro h
    have hd := h.2
    simpa only [hw, mfld_simps, hasFDerivWithinAt_univ] using! hd
  · intro hd
    constructor
    · have h := coord.symm.continuous.continuousAt.comp hd.continuousAt
      simpa only [Function.comp_def, coord.symm_apply_apply] using h
    · simpa only [hw, mfld_simps] using! (hd.hasFDerivWithinAt (s := Set.univ))

set_option backward.isDefEq.respectTransparency false in
/-- A proved original coordinate derivative gives the same actual
manifold tangent when the scalar differential is applied to one. -/
theorem original_curve_lie_tangent (coord : G ≃ₜ E) (gamma : ℝ → G)
    (t : ℝ) (v : E) (hv : HasDerivAt (coord ∘ gamma) v t) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma t (1 : ℝ) = v := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  have h := (original_curve_has_mfderiv_iff coord gamma t _).mpr hv.hasFDerivAt
  rw [h.mfderiv]
  change (ContinuousLinearMap.toSpanSingleton ℝ v) (1 : ℝ) = v
  simp

end GMZP0
