import GMZP0.OriginalBoundedWeakBasis
import GMZP0.RationalLowerCentral

/-! Lower-central rationality and bounded bases on the actual native Lie
algebra in the same original chart and original weak-basis witnesses. -/
noncomputable section
open Module
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]

/-- A smooth original real Lie group has exactly the regularity required
by Mathlib's native Lie-ring instance. No extra smoothness is assumed. -/
theorem original_real_lie_native_smoothness [ChartedSpace (sigma → ℝ) G]
    [LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G] : LieGroup 𝓘(ℝ, sigma → ℝ) (minSmoothness ℝ 3) G := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : LieGroup 𝓘(ℝ, sigma → ℝ) (3 : ℕ∞ω) G)

attribute [local instance] original_real_lie_native_smoothness

/-- The actual native lower-central ideals are rational in the original
tangent basis, not in a separately defined coordinate Lie algebra. -/
theorem original_weak_basis_lower_central_rational (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ n : ℕ, RationalInBasis (originalTangentBasis coord)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
        (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  obtain ⟨C, hC⟩ := hweak.rational_bracket
  exact fun n => rational_lower_central_in_basis (originalTangentBasis coord) C
    (fun i j k => (hC i j k).1) n

/-- One bound precedes every layer up to the fixed depth and every
coordinate of actual lower-central bases in the original native Lie algebra. -/
theorem original_weak_basis_lower_central_bases (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ)
    (hweak : OriginalWeakBasisBound coord Gamma logCoord Q)
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ r : ℕ, ∃ H : ℕ, 2 < H ∧ ∀ n ≤ r,
      ∃ J : Set (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G), J.Finite ∧
        ∃ bN : Basis J ℝ (LieModule.lowerCentralSeries ℝ
          (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) n).toSubmodule,
          ∀ j : J, ∃ a : sigma → ℚ, ∀ i,
            (originalTangentBasis coord).repr (bN j : GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) i =
              (a i : ℝ) ∧ rationalHeight (a i) ≤ H := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  obtain ⟨C, hC⟩ := hweak.rational_bracket
  exact fun r => rational_lower_central_bounded_bases (originalTangentBasis coord) C
    (fun i j k => (hC i j k).1) r

end GMZP0
