import GMZP0.OriginalConjugationTangent
import GMZP0.OriginalExponentialSubspace

/-! Equivariance under actual original conjugation, derived from native
subgroup uniqueness. No Lie-bracket preservation is assumed. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]

/-- The same original exponential intertwines the actual tangent action
and actual group conjugation, for every unrestricted original vector. -/
theorem original_weak_basis_adjoint_exp (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) (v : sigma → ℝ) :
    logCoord.symm (originalAdjoint coord g v) = g * logCoord.symm v * g⁻¹ := by
  have hc := original_native_subgroup_conjugate coord hLie g _ v (hweak.native_subgroups v).1
  have he := (hweak.native_subgroups (originalAdjoint coord g v)).2 _ hc
  simpa only [one_smul] using (congrFun he 1).symm

/-- Original logarithms of conjugates are exactly the original tangent
action applied to the original logarithm. -/
theorem original_weak_basis_adjoint_log (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g h : G) :
    logCoord (g * h * g⁻¹) = originalAdjoint coord g (logCoord h) := by
  simpa using (congrArg logCoord
    (original_weak_basis_adjoint_exp coord Gamma logCoord Q hweak hLie g (logCoord h))).symm

/-- The tangent action of the original identity is the identity. -/
theorem original_weak_basis_adjoint_one (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) :
    originalAdjoint coord 1 = ContinuousLinearMap.id ℝ (sigma → ℝ) := by
  apply ContinuousLinearMap.ext
  intro v
  apply logCoord.symm.injective
  simpa using original_weak_basis_adjoint_exp coord Gamma logCoord Q hweak hLie 1 v

/-- Composition follows the actual original group order. -/
theorem original_weak_basis_adjoint_mul (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g h : G) :
    originalAdjoint coord (g * h) = (originalAdjoint coord g).comp (originalAdjoint coord h) := by
  apply ContinuousLinearMap.ext
  intro v
  apply logCoord.symm.injective
  simp only [ContinuousLinearMap.comp_apply,
    original_weak_basis_adjoint_exp coord Gamma logCoord Q hweak hLie,
    mul_inv_rev, mul_assoc]

/-- Conjugation stability of the actual exponential set is equivalent to
stability under the actual tangent action. This equivalence does not
postulate that a Lie ideal already has either stability property. -/
theorem original_exponential_image_conjugation_iff (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (U : Submodule ℝ (sigma → ℝ)) :
    (∀ g h, h ∈ originalExponentialImage logCoord U →
      g * h * g⁻¹ ∈ originalExponentialImage logCoord U) ↔
    ∀ g v, v ∈ U → originalAdjoint coord g v ∈ U := by
  constructor
  · intro h g v hv
    have hm : logCoord.symm v ∈ originalExponentialImage logCoord U := by
      change logCoord (logCoord.symm v) ∈ U
      simpa using hv
    have hr := h g (logCoord.symm v) hm
    change logCoord (g * logCoord.symm v * g⁻¹) ∈ U at hr
    simpa only [original_weak_basis_adjoint_log coord Gamma logCoord Q hweak hLie,
      logCoord.apply_symm_apply] using hr
  · intro h g a ha
    change logCoord (g * a * g⁻¹) ∈ U
    rw [original_weak_basis_adjoint_log coord Gamma logCoord Q hweak hLie]
    exact h g (logCoord a) ha

end GMZP0
