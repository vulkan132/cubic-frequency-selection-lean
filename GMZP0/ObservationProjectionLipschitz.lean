import GMZP0.ObservationMetricLifts
import GMZP0.UniformLocalProjection

/-! The original quotient projection's uniform Lipschitz constant is
derived from compactness and controlled actual pair lifts. -/
noncomputable section
open Set Metric Module
open scoped NNReal
namespace GMZP0
variable {G : Type*} [Group G] [PseudoMetricSpace G]
  (V : ObservationModule G) (Gamma : Subgroup G)
  [MetricSpace (G ⧸ Gamma)]
  [PseudoMetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]

local instance originalProjectionMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : MetricSpace (G ⧸ Gamma)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Actual nearby base lifts give the local bound for the original
quotient projection. The literal base coset metric retains all translates. -/
theorem original_projection_local_bound
    (hdistG : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (B r : ℝ)
    (hlift : ∀ x y : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma, dist x y < r →
      ∃ u v : ObservationGroup V, QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧
        dist u.base v.base ≤ B * dist x y) :
    ∀ x y, dist x y < r →
      dist (observationQuotientBaseProjection V Gamma x) (observationQuotientBaseProjection V Gamma y) ≤
        B * dist x y := by
  intro x y hxy
  obtain ⟨u, v, hu, hv, hbase⟩ := hlift x y hxy
  have h := (quotient_mk_lipschitz_of_coset_formula Gamma hdistG).dist_le_mul u.base v.base
  simp only [NNReal.coe_one, one_mul] at h
  have hux : observationQuotientBaseProjection V Gamma x = QuotientGroup.mk u.base := by
    rw [← hu]
    rfl
  have hvy : observationQuotientBaseProjection V Gamma y = QuotientGroup.mk v.base := by
    rw [← hv]
    rfl
  rw [hux, hvy]
  exact h.trans hbase

/-- The compact original base cover supplies boundedness in the actual
base quotient metric, so one global projection constant is proved. -/
theorem original_projection_lipschitz_of_lifts
    (K₀ : Set G) (hK₀ : IsCompact K₀)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K₀)
    (hdistG : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r)
    (hlift : ∀ x y : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma, dist x y < r →
      ∃ u v : ObservationGroup V, QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧
        dist u.base v.base ≤ B * dist x y) :
    ∃ J : ℝ≥0, LipschitzWith J (observationQuotientBaseProjection V Gamma) := by
  let : CompactSpace (G ⧸ Gamma) := coset_metric_compact_of_cover Gamma K₀ hK₀ hcover hdistG
  exact ⟨_, lipschitz_of_uniform_local_bound (observationQuotientBaseProjection V Gamma)
    B r hB hr (original_projection_local_bound V Gamma hdistG B r hlift)
    (isCompact_univ.isBounded.subset (Set.subset_univ _))⟩

end GMZP0
