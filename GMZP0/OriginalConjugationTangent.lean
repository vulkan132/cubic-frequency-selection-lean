import GMZP0.OriginalSubgroupTangent

/-! The actual differential of conjugation, on the original chart and
native tangent space. Differentiability follows from the original smooth
group structure, rather than from a totalized derivative value. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0
variable {G E : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Both directions of the native/coordinate differential identification
for a self-map in the actual singleton chart. -/
theorem original_self_map_has_mfderiv_iff (coord : G ≃ₜ E) (f : G → G)
    (x : G) (D : E →L[ℝ] E) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x D ↔
      HasFDerivAt (coord ∘ f ∘ coord.symm) D (coord x) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  constructor
  · intro h
    have hd := h.2
    simpa only [original_written_in_chart, original_ext_chart,
      modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] using! hd
  · exact original_has_mfderiv coord f x D

/-- The original conjugation map in literal original coordinates. -/
def originalConjugationCoordinates (coord : G ≃ₜ E) (g : G) : E → E :=
  coord ∘ (fun h => g * h * g⁻¹) ∘ coord.symm

/-- The derivative at the original identity; it will be identified with
the actual native differential, with differentiability proved separately. -/
def originalAdjoint (coord : G ≃ₜ E) (g : G) : E →L[ℝ] E :=
  fderiv ℝ (originalConjugationCoordinates coord g) (coord 1)

/-- Actual smooth group operations imply differentiability of conjugation
in the original chart at the original identity. -/
theorem original_conjugation_differentiable (coord : G ≃ₜ E)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, E) ∞ G) (g : G) :
    DifferentiableAt ℝ (originalConjugationCoordinates coord g) (coord 1) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun h : G => g * h * g⁻¹) :=
    (contMDiff_const.mul contMDiff_id).mul contMDiff_const
  have hd := (h.contMDiffAt (x := (1 : G))).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  exact ((original_self_map_has_mfderiv_iff coord _ 1 _).mp hd.hasMFDerivAt).differentiableAt

/-- This is exactly the original native tangent differential, not an
unrelated coordinate action. -/
theorem original_adjoint_native (coord : G ≃ₜ E)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, E) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => g * h * g⁻¹) 1 = originalAdjoint coord g := by
  exact original_mfderiv coord _ 1 (original_conjugation_differentiable coord hLie g)

/-- Conjugating an original native subgroup sends its actual initial
tangent through the actual conjugation differential. -/
theorem original_native_subgroup_conjugate (coord : G ≃ₜ E)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, E) ∞ G) (g : G) (gamma : ℝ → G) (v : E)
    (hgamma : OriginalNativeSubgroup coord gamma v) :
    OriginalNativeSubgroup coord (fun t => g * gamma t * g⁻¹) (originalAdjoint coord g v) := by
  have hd := (original_coordinate_derivative_iff_native coord gamma v).mpr hgamma.2.2
  have hf := (original_conjugation_differentiable coord hLie g).hasFDerivAt
  have hp := hf.comp_hasDerivAt_of_eq 0 hd (by simp only [Function.comp_apply, hgamma.1])
  have hderiv : HasDerivAt (coord ∘ (fun t => g * gamma t * g⁻¹))
      (originalAdjoint coord g v) 0 := by
    simpa only [originalAdjoint, originalConjugationCoordinates, Function.comp_def,
      coord.symm_apply_apply] using hp
  refine ⟨?_, ?_, (original_coordinate_derivative_iff_native coord _ _).mp hderiv⟩
  · simp only [hgamma.1, mul_one, mul_inv_cancel]
  · intro s t
    simp only [hgamma.2.1, mul_assoc, inv_mul_cancel_left]

end GMZP0
