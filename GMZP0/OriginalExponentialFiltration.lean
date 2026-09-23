import GMZP0.OriginalExponentialSubspace
import GMZP0.RationalSubspaceLattice
import GMZP0.OriginalRationalLowerCentral

/-! Topology, powers and exact original-lattice spans for exponential
images of the actual native lower-central ideals. Group integration is
not an input and is not claimed as a conclusion. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]

/-- Data on the actual exponential set, deliberately without a subgroup
structure. The finite spanning set consists of original lattice points. -/
structure OriginalExponentialSubspaceData (Gamma : Subgroup G)
    (logCoord : G ≃ (sigma → ℝ)) (U : Submodule ℝ (sigma → ℝ)) : Prop where
  closed : IsClosed (originalExponentialImage logCoord U)
  contractible : ContractibleSpace (originalExponentialImage logCoord U)
  one_mem : 1 ∈ originalExponentialImage logCoord U
  inv_mem : ∀ g ∈ originalExponentialImage logCoord U, g⁻¹ ∈ originalExponentialImage logCoord U
  power_mem_iff : ∀ g (n : ℕ), 0 < n →
    (g ^ n ∈ originalExponentialImage logCoord U ↔ g ∈ originalExponentialImage logCoord U)
  finite_lattice_span : ∃ F : Finset G, (∀ g ∈ F, g ∈ Gamma ∧ logCoord g ∈ U) ∧
    Submodule.span ℝ (logCoord '' (F : Set G)) = U
  lattice_span : Submodule.span ℝ (logCoord '' {g | g ∈ Gamma ∧ logCoord g ∈ U}) = U

/-- All conclusions use the same original weak basis and the actual
logarithm whose rational arrays were constructed from the original group. -/
theorem original_weak_basis_exponential_subspace_data (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (S T : sigma → MvPolynomial sigma ℚ)
    (hS : ∀ x i, coord (logCoord.symm x) i = MvPolynomial.aeval x (S i))
    (hT : ∀ a i, logCoord a i = MvPolynomial.aeval (coord a) (T i))
    (U : Submodule ℝ (sigma → ℝ)) (hU : RationalInBasis (Pi.basisFun ℝ sigma) U) :
    OriginalExponentialSubspaceData Gamma logCoord U := by
  let logHomeo := originalLogHomeomorph coord logCoord S T hS hT
  have hp := original_exponential_image_power_properties coord Gamma logCoord Q hweak U
  obtain ⟨den, hden, _, hgrid, _⟩ := hweak.lattice_denominator
  exact ⟨original_exponential_image_closed logHomeo U,
    original_exponential_image_contractible logHomeo U, hp.1, hp.2.1, hp.2.2,
    rational_subspace_finite_original_lattice_span Gamma logCoord den hden hgrid U hU,
    rational_subspace_original_lattice_span Gamma logCoord den hden hgrid U hU⟩

attribute [local instance] original_real_lie_native_smoothness

/-- Apply the exact-set conclusions to every actual native Lie lower-central
ideal. These are the same witnesses delivered by the full F63 construction;
no group/Lie lower-central correspondence is postulated. -/
theorem original_weak_basis_lower_central_exponential_data (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (S T : sigma → MvPolynomial sigma ℚ)
    (hS : ∀ x i, coord (logCoord.symm x) i = MvPolynomial.aeval x (S i))
    (hT : ∀ a i, logCoord a i = MvPolynomial.aeval (coord a) (T i))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ n : ℕ, OriginalExponentialSubspaceData Gamma logCoord
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
        (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  intro n
  apply original_weak_basis_exponential_subspace_data coord Gamma logCoord Q hweak S T hS hT
  exact original_weak_basis_lower_central_rational coord Gamma logCoord Q hweak hLie n

end GMZP0
