import GMZP0.PolynomialCoordinateMetric

/-! A compatible right-invariant source metric is constructed directly
from an original finite-dimensional coordinate homeomorphism and literal
joint polynomial group multiplication. Both coordinate directions are
locally Lipschitz for that constructed metric. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {iota : Type*} [Fintype iota]

/-- All source metric, right-isometry and local coordinate regularity
requirements are derived from the same actual polynomial coordinate law. -/
theorem polynomial_group_right_metric
    (coord : G ≃ₜ (iota → ℝ)) (p : iota → MvPolynomial (iota ⊕ iota) ℝ)
    (hgroup : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i)) :
    ∃ m : MetricSpace G, m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
      (∀ a : G, @Isometry G G m.toPseudoEMetricSpace m.toPseudoEMetricSpace (fun x => x * a)) ∧
      @LocallyLipschitz G (iota → ℝ) m.toPseudoEMetricSpace inferInstance coord ∧
      @LocallyLipschitz (iota → ℝ) G inferInstance m.toPseudoEMetricSpace coord.symm := by
  let m₀ := originalCoordinateMetric coord
  let : ProperSpace G := original_coordinate_metric_proper coord
  have hmul : LocallyLipschitz (fun z : G × G => z.1 * z.2) :=
    polynomial_coordinate_multiplication_locally_lipschitz coord p hgroup
  have hc : Isometry coord := original_coordinate_metric_isometry coord
  have hi : Isometry coord.symm := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (coord (coord.symm x)) (coord (coord.symm y)) = dist x y
    simp
  have hbi := compatible_right_metric_local_comparison hmul
  let m₁ := compatibleRightMetric hmul
  let : MetricSpace G := m₀
  refine ⟨m₁, rfl, compatible_right_metric_isometry hmul, ?_, ?_⟩
  · exact @LocallyLipschitz.comp G G (iota → ℝ) m₁.toPseudoEMetricSpace
      m₀.toPseudoEMetricSpace inferInstance coord id hc.lipschitz.locallyLipschitz hbi.2
  · exact @LocallyLipschitz.comp (iota → ℝ) G G inferInstance
      m₀.toPseudoEMetricSpace m₁.toPseudoEMetricSpace id coord.symm hbi.1 hi.lipschitz.locallyLipschitz

end GMZP0
