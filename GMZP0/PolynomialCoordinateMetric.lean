import GMZP0.CompatibleRightMetric
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Ordinary polynomial coordinate multiplication supplies the local
regularity required by the right-invariant metric construction. -/
noncomputable section
open Set Metric
namespace GMZP0

/-- A literal multivariate polynomial in C1 scalar coordinate functions
is C1; no smoothness of an abstract Lie group is supplied as an input. -/
theorem coordinate_polynomial_contDiff {sigma E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : MvPolynomial sigma ℝ) (v : E → sigma → ℝ)
    (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i)) :
    ContDiff ℝ 1 (fun x => MvPolynomial.aeval (v x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : E => a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hv i)

/-- A fixed finite collection of literal joint coordinate polynomials
defines a locally Lipschitz multiplication map in coordinate space. -/
theorem joint_coordinate_polynomials_locally_lipschitz {iota : Type*} [Fintype iota]
    (p : iota → MvPolynomial (iota ⊕ iota) ℝ) :
    LocallyLipschitz (fun z : (iota → ℝ) × (iota → ℝ) =>
      fun i => MvPolynomial.aeval (Sum.elim z.1 z.2) (p i)) := by
  apply ContDiff.locallyLipschitz (𝕂 := ℝ)
  apply contDiff_pi.mpr
  intro i
  apply coordinate_polynomial_contDiff
  intro j
  cases j with
  | inl j => exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
  | inr j => exact (contDiff_apply ℝ ℝ j).comp contDiff_snd

variable {G : Type*} [TopologicalSpace G] {iota : Type*} [Fintype iota]

/-- The initial coordinate metric preserves the given original topology. -/
@[instance_reducible] def originalCoordinateMetric (coord : G ≃ₜ (iota → ℝ)) : MetricSpace G :=
  @MetricSpace.replaceTopology G inferInstance
    (MetricSpace.induced coord coord.injective inferInstance) coord.isInducing.eq_induced

/-- The supplied coordinate homeomorphism is an isometry for the initial
coordinate metric, before the right-invariant replacement. -/
theorem original_coordinate_metric_isometry (coord : G ≃ₜ (iota → ℝ)) :
    @Isometry G (iota → ℝ) (originalCoordinateMetric coord).toPseudoEMetricSpace
      inferInstance coord := by
  apply (@isometry_iff_dist_eq G (iota → ℝ) (originalCoordinateMetric coord).toPseudoMetricSpace
    inferInstance coord).mpr
  exact fun _ _ => rfl

/-- Finite-dimensional coordinate balls are compact in the initial
metric, with the exact original topology. -/
theorem original_coordinate_metric_proper (coord : G ≃ₜ (iota → ℝ)) :
    @ProperSpace G (originalCoordinateMetric coord).toPseudoMetricSpace := by
  let := originalCoordinateMetric coord
  constructor
  intro g r
  have he : closedBall g r = coord.symm '' closedBall (coord g) r := by
    ext x
    constructor
    · intro hx
      exact ⟨coord x, hx, coord.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change dist (coord (coord.symm y)) (coord g) ≤ r
      simpa using hy
  rw [he]
  exact (isCompact_closedBall _ _).image coord.symm.continuous

variable [Group G]

/-- Literal joint polynomial group laws prove local Lipschitz
multiplication for the constructed initial coordinate metric. -/
theorem polynomial_coordinate_multiplication_locally_lipschitz
    (coord : G ≃ₜ (iota → ℝ)) (p : iota → MvPolynomial (iota ⊕ iota) ℝ)
    (hgroup : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i)) :
    letI := originalCoordinateMetric coord
    LocallyLipschitz (fun z : G × G => z.1 * z.2) := by
  let := originalCoordinateMetric coord
  have hc : Isometry coord := original_coordinate_metric_isometry coord
  have hi : Isometry coord.symm := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (coord (coord.symm x)) (coord (coord.symm y)) = dist x y
    simp
  have hp := (hc.lipschitz.comp LipschitzWith.prod_fst).prodMk (hc.lipschitz.comp LipschitzWith.prod_snd)
  have hF := joint_coordinate_polynomials_locally_lipschitz p
  have hcomp := hi.lipschitz.locallyLipschitz.comp (hF.comp hp.locallyLipschitz)
  convert hcomp using 1
  funext z
  apply coord.injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  exact funext (hgroup z.1 z.2)

end GMZP0
