import GMZP0.OriginalNativeExponential
import GMZP0.RationalHeightFinite

/-! Bounded weak-basis data for the actual original Lie algebra and
lattice. The first-kind coordinates are certified by native subgroups;
one common structural bound controls heights and the lattice denominator. -/
noncomputable section
open Module
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]

/-- The quantitative weak-basis clauses on the actual original tangent
basis. Adapted filtration subgroups and external metric data are separate. -/
structure OriginalWeakBasisBound (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) (Q : ℕ) : Prop where
  two_lt : 2 < Q
  native_subgroups : ∀ v : sigma → ℝ,
    OriginalNativeSubgroup coord (fun t : ℝ => logCoord.symm (t • v)) v ∧
    ∀ eta, OriginalNativeSubgroup coord eta v → eta = (fun t : ℝ => logCoord.symm (t • v))
  rational_bracket :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    ∃ C : sigma → sigma → sigma → ℚ, ∀ i j k,
      (originalTangentBasis coord).repr
        ⁅originalTangentBasis coord i, originalTangentBasis coord j⁆ k = (C i j k : ℝ) ∧
      rationalHeight (C i j k) ≤ Q
  lattice_denominator : ∃ den : ℕ, 0 < den ∧ den ≤ Q ∧
    (∀ z : sigma → ℤ, ∃ gamma : Gamma, ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ)) ∧
    (∀ gamma : Gamma, ∃ z : sigma → ℤ, ∀ i, (den : ℝ) * logCoord gamma i = z i)

/-- Explicit fixed bound for the rational tensor and lattice denominator. -/
def originalWeakBasisHeight (C : sigma → sigma → sigma → ℚ) (den : ℕ) : ℕ :=
  max 3 (max den (rationalArrayHeight (fun z : sigma × sigma × sigma => C z.1 z.2.1 z.2.2)))

/-- A single common bound supplies the actual weak-basis input; it is
chosen from fixed structure constants and a fixed lattice denominator. -/
theorem original_weak_basis_from_native_data (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ))
    (C : sigma → sigma → sigma → ℚ) (den : ℕ)
    (hnative : ∀ v : sigma → ℝ,
      OriginalNativeSubgroup coord (fun t : ℝ => logCoord.symm (t • v)) v ∧
      ∀ eta, OriginalNativeSubgroup coord eta v → eta = (fun t : ℝ => logCoord.symm (t • v)))
    (hbracket : letI := coord.isOpenEmbedding.singletonChartedSpace;
      ∀ i j k, (originalTangentBasis coord).repr
        ⁅originalTangentBasis coord i, originalTangentBasis coord j⁆ k = (C i j k : ℝ))
    (hden : 0 < den)
    (hleft : ∀ z : sigma → ℤ, ∃ gamma : Gamma,
      ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ))
    (hright : ∀ gamma : Gamma, ∃ z : sigma → ℤ,
      ∀ i, (den : ℝ) * logCoord gamma i = z i) :
    OriginalWeakBasisBound coord Gamma logCoord (originalWeakBasisHeight C den) := by
  refine ⟨lt_of_lt_of_le (by decide : 2 < (3 : ℕ)) (le_max_left _ _), hnative, ?_,
    ⟨den, hden, (le_max_left _ _).trans (le_max_right _ _), hleft, hright⟩⟩
  let := coord.isOpenEmbedding.singletonChartedSpace
  refine ⟨C, ?_⟩
  intro i j k
  refine ⟨hbracket i j k, ?_⟩
  exact (rational_array_height_bound (fun z : sigma × sigma × sigma => C z.1 z.2.1 z.2.2)
    (i, j, k)).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Enlarging the common bound preserves all native and original-lattice
clauses, so additional fixed structural costs can share that same bound. -/
theorem original_weak_basis_bound_mono (coord : G ≃ₜ (sigma → ℝ))
    (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ)) {Q R : ℕ}
    (h : OriginalWeakBasisBound coord Gamma logCoord Q) (hQR : Q ≤ R) :
    OriginalWeakBasisBound coord Gamma logCoord R := by
  refine ⟨h.two_lt.trans_le hQR, h.native_subgroups, ?_, ?_⟩
  · let := coord.isOpenEmbedding.singletonChartedSpace
    obtain ⟨C, hC⟩ := h.rational_bracket
    exact ⟨C, fun i j k => ⟨(hC i j k).1, (hC i j k).2.trans hQR⟩⟩
  · obtain ⟨den, hp, hd, hl, hr⟩ := h.lattice_denominator
    exact ⟨den, hp, hd.trans hQR, hl, hr⟩

end GMZP0
