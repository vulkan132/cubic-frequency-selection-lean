import GMZP0.ObservationMultiplicationPolynomials
import GMZP0.PolynomialGroupRightMetric

/-! Construct the actual G/H source metrics from the original polynomial
presentation, including local regularity of the actual base and fiber maps. -/
noncomputable section
open Module
namespace GMZP0

/-- Restricting a finite coordinate vector along any fixed index map is
1-Lipschitz for the actual coordinate sup norms. -/
theorem finite_coordinate_restriction_lipschitz {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] (r : beta → alpha) :
    LipschitzWith 1 (fun v : alpha → ℝ => fun j => v (r j)) := by
  apply LipschitzWith.mk_one
  intro v w
  exact (dist_pi_le_iff dist_nonneg).mpr fun j => dist_le_pi_dist v w (r j)

variable {G sigma iota : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype sigma] [Fintype iota]

/-- Both original source metrics, all original right isometries and the
actual base/fiber local regularity are derived from the original base law
and basis functions. No H coordinate law, metric or regularity is supplied. -/
theorem original_observation_source_metrics
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℝ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ mG : MetricSpace G, ∃ mH : MetricSpace (ObservationGroup V),
      mG.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
      mH.toUniformSpace.toTopologicalSpace = observationGroupTopology V ∧
      (∀ a : G, @Isometry G G mG.toPseudoEMetricSpace mG.toPseudoEMetricSpace (fun x => x * a)) ∧
      (∀ a : ObservationGroup V, @Isometry (ObservationGroup V) (ObservationGroup V)
        mH.toPseudoEMetricSpace mH.toPseudoEMetricSpace (fun x => x * a)) ∧
      @LocallyLipschitz G (sigma → ℝ) mG.toPseudoEMetricSpace inferInstance coord ∧
      @LocallyLipschitz (sigma → ℝ) G inferInstance mG.toPseudoEMetricSpace coord.symm ∧
      @LocallyLipschitz (ObservationGroup V) G mH.toPseudoEMetricSpace mG.toPseudoEMetricSpace
        (fun a => a.base) ∧
      @LocallyLipschitz (ObservationGroup V) (iota → ℝ) mH.toPseudoEMetricSpace inferInstance
        (fun a => b.equivFun a.obs) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  let : IsTopologicalGroup (ObservationGroup V) := observation_isTopologicalGroup V
    (observation_basis_polynomials_continuous V coord b P hP)
  obtain ⟨Q, hQ⟩ := observation_group_joint_polynomial_presentation V coord b p hgroup P hP
  obtain ⟨mG, htG, hrG, hcG, hiG⟩ := polynomial_group_right_metric coord p hgroup
  obtain ⟨mH, htH, hrH, hcH, _⟩ := polynomial_group_right_metric
    (observationFullCoordinates V coord b) Q hQ
  have hbaseCoords := @LocallyLipschitz.comp (ObservationGroup V)
    ((sigma ⊕ iota) → ℝ) (sigma → ℝ) mH.toPseudoEMetricSpace inferInstance inferInstance
    (fun v j => v (Sum.inl j)) (observationFullCoordinates V coord b)
    (finite_coordinate_restriction_lipschitz (Sum.inl : sigma → sigma ⊕ iota)).locallyLipschitz hcH
  have hbase := @LocallyLipschitz.comp (ObservationGroup V) (sigma → ℝ) G
    mH.toPseudoEMetricSpace inferInstance mG.toPseudoEMetricSpace coord.symm
    (fun a j => observationFullCoordinates V coord b a (Sum.inl j)) hiG hbaseCoords
  have hfiber := @LocallyLipschitz.comp (ObservationGroup V)
    ((sigma ⊕ iota) → ℝ) (iota → ℝ) mH.toPseudoEMetricSpace inferInstance inferInstance
    (fun v j => v (Sum.inr j)) (observationFullCoordinates V coord b)
    (finite_coordinate_restriction_lipschitz (Sum.inr : iota → sigma ⊕ iota)).locallyLipschitz hcH
  refine ⟨mG, mH, htG, htH, hrG, hrH, hcG, hiG, ?_, hfiber⟩
  convert hbase using 1
  funext a
  exact (coord.symm_apply_apply a.base).symm

end GMZP0
