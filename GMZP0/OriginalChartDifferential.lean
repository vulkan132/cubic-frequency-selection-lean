import GMZP0.RationalCoordinateLieGroup
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Actual manifold differentials in the original singleton global chart.
These identities retain the original underlying space and topology. -/
noncomputable section
open scoped Manifold
namespace GMZP0
variable {G E : Type*} [TopologicalSpace G] [Nonempty G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The preferred extended chart is exactly the original global coordinates. -/
theorem original_ext_chart (coord : G ≃ₜ E) (x : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    ⇑(extChartAt 𝓘(ℝ, E) x) = coord := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  rw [extChartAt_coe, coord.isOpenEmbedding.singletonChartedSpace_chartAt_eq]
  rfl

/-- The inverse preferred chart is the inverse of the same original coordinates. -/
theorem original_ext_chart_symm (coord : G ≃ₜ E) (x : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    ⇑(extChartAt 𝓘(ℝ, E) x).symm = coord.symm := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  funext y
  obtain ⟨z, rfl⟩ := coord.surjective y
  change (coord.isOpenEmbedding.toOpenPartialHomeomorph coord).symm (coord z) = coord.symm (coord z)
  rw [coord.isOpenEmbedding.toOpenPartialHomeomorph_left_inv, coord.symm_apply_apply]

/-- Writing a self-map in the original charts is literal coordinate conjugation. -/
theorem original_written_in_chart (coord : G ≃ₜ E) (f : G → G) (x : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x f = coord ∘ f ∘ coord.symm := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  simp only [writtenInExtChartAt, original_ext_chart, original_ext_chart_symm]

set_option backward.isDefEq.respectTransparency false in
/-- A derivative of the actual coordinate conjugate is the manifold
derivative in the original global chart. -/
theorem original_has_mfderiv (coord : G ≃ₜ E) (f : G → G) (x : G)
    (D : E →L[ℝ] E) (hD : HasFDerivAt (coord ∘ f ∘ coord.symm) D (coord x)) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x D := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  constructor
  · have h := coord.symm.continuous.continuousAt.comp
      (hD.continuousAt.comp coord.continuous.continuousAt)
    simpa only [Function.comp_def, coord.symm_apply_apply] using h
  · simpa only [original_written_in_chart, original_ext_chart,
      modelWithCornersSelf_coe, Set.range_id] using! (hD.hasFDerivWithinAt (s := Set.univ))

/-- The actual manifold differential equals the analytic coordinate
differential whenever that coordinate map is differentiable. -/
theorem original_mfderiv (coord : G ≃ₜ E) (f : G → G) (x : G)
    (hf : DifferentiableAt ℝ (coord ∘ f ∘ coord.symm) (coord x)) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x = fderiv ℝ (coord ∘ f ∘ coord.symm) (coord x) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  exact (original_has_mfderiv coord f x _ hf.hasFDerivAt).mfderiv

end GMZP0
