import GMZP0.OriginalAdjointLieBracket
import GMZP0.OriginalAdjointExponential
import GMZP0.OriginalExponentialFiltration

/-! Actual native lower-central ideals and their actual exponential sets
are stable under original conjugation. Multiplicative closure of the sets
and their identification with group lower-central subgroups remain separate. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]
attribute [local instance] original_real_lie_native_smoothness

/-- The actual tangent conjugation preserves each native Lie lower-central
ideal, by the proved Lie homomorphism and Mathlib's actual ideal-map theorem. -/
theorem original_adjoint_lower_central_mem (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ n (v : GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G),
      v ∈ LieModule.lowerCentralSeries ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
        (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n →
      originalAdjoint coord g v ∈ LieModule.lowerCentralSeries ℝ
        (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  intro n v hv
  exact LieIdeal.map_lowerCentralSeries_le n (f := originalAdjointLieHom coord hLie g)
    (LieIdeal.mem_map hv)

/-- Every exponential lower-central set is invariant under conjugation
by every original group element, in both directions. It is still a set. -/
theorem original_lower_central_exponential_conjugation_iff (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ n (g h : G),
      (g * h * g⁻¹ ∈ originalExponentialImage logCoord
        (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
          (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule) ↔
      h ∈ originalExponentialImage logCoord
        (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
          (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  intro n
  have hstable := (original_exponential_image_conjugation_iff coord Gamma logCoord Q hweak hLie
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
      (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule).mpr
    (fun g v hv => original_adjoint_lower_central_mem coord hLie g n v hv)
  intro g h
  constructor
  · intro hh
    have hs := hstable g⁻¹ (g * h * g⁻¹) hh
    simpa [mul_assoc] using hs
  · exact hstable g h

/-- Combine conjugation invariance with all F64 exact-set and original-
lattice properties using the same original weak basis and literal arrays. -/
theorem original_lower_central_conjugation_data (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (S T : sigma → MvPolynomial sigma ℚ)
    (hS : ∀ x i, coord (logCoord.symm x) i = MvPolynomial.aeval x (S i))
    (hT : ∀ a i, logCoord a i = MvPolynomial.aeval (coord a) (T i))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ n : ℕ, let U := (LieModule.lowerCentralSeries ℝ
      (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule;
      OriginalExponentialSubspaceData Gamma logCoord U ∧
        ∀ g h : G, (g * h * g⁻¹ ∈ originalExponentialImage logCoord U ↔
          h ∈ originalExponentialImage logCoord U) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  intro n
  exact ⟨original_weak_basis_lower_central_exponential_data coord Gamma logCoord Q
    hweak S T hS hT hLie n,
    original_lower_central_exponential_conjugation_iff coord Gamma logCoord Q hweak hLie n⟩

end GMZP0
