import GMZP0.PolynomialGroupRightMetric
import GMZP0.OriginalCosetMetric

/-! The actual source and quotient metrics are both derived from literal
polynomial coordinates and the original discrete lattice compact cover. -/
noncomputable section
open Set
namespace GMZP0
variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {iota : Type*} [Fintype iota]

/-- No source metric, quotient metric, isometry or local coordinate
regularity is supplied: all are constructed from the actual coordinate
law and original compact lattice cover, without normality. -/
theorem polynomial_group_and_coset_metrics
    (coord : G ≃ₜ (iota → ℝ)) (p : iota → MvPolynomial (iota ⊕ iota) ℝ)
    (hgroup : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (K : Set G) (hK : IsCompact K) (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K) :
    ∃ mG : MetricSpace G, ∃ mQ : MetricSpace (G ⧸ Gamma),
      mG.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
      mQ.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Gamma ∧
      (∀ a : G, @Isometry G G mG.toPseudoEMetricSpace mG.toPseudoEMetricSpace (fun x => x * a)) ∧
      @LocallyLipschitz G (iota → ℝ) mG.toPseudoEMetricSpace inferInstance coord ∧
      @LocallyLipschitz (iota → ℝ) G inferInstance mG.toPseudoEMetricSpace coord.symm ∧
      ∀ g h : G, @dist (G ⧸ Gamma) mQ.toDist (QuotientGroup.mk g) (QuotientGroup.mk h) =
        @originalCosetInfDist G _ mG.toPseudoMetricSpace Gamma g h := by
  obtain ⟨m, htop, hright, hc, hi⟩ := polynomial_group_right_metric coord p hgroup
  let mG := @MetricSpace.replaceTopology G (inferInstance : TopologicalSpace G) m htop.symm
  have heq : mG = m := MetricSpace.replaceTopology_eq _ _
  have hr : ∀ a : G, @Isometry G G mG.toPseudoEMetricSpace mG.toPseudoEMetricSpace (fun x => x * a) := by
    rw [heq]
    exact hright
  have hc' : @LocallyLipschitz G (iota → ℝ) mG.toPseudoEMetricSpace inferInstance coord := by
    rw [heq]
    exact hc
  have hi' : @LocallyLipschitz (iota → ℝ) G inferInstance mG.toPseudoEMetricSpace coord.symm := by
    rw [heq]
    exact hi
  have hclosed : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  let mQ := originalCosetMetric Gamma hclosed (fun a => hr a) K hK hcover
  exact ⟨mG, mQ, rfl, rfl, hr, hc', hi', fun _ _ => rfl⟩

end GMZP0
