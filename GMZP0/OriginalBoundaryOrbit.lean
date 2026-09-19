import GMZP0.BoundaryOrbitEstimate
import GMZP0.ObservationMeasurability

/-! Apply the boundary estimate to the unchanged original quotient observation.
Zero mean is proved by its actual constant-translation symmetry, not supplied
as a new premise. Quantitative metric and geometric inputs remain explicit. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped NNReal
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  (V : ObservationModule G) [FiniteDimensional ℝ V.space] (Gamma : Subgroup G)
  [PseudoMetricSpace (G ⧸ Gamma)]

-- The supplied metric uses the original quotient measurable space. Its
-- Borel compatibility is explicit; no quantitative Malcev metric is inferred.
local instance originalBoundaryMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : PseudoMetricSpace (G ⧸ Gamma)).toUniformSpace.toTopologicalSpace

variable [BorelSpace (G ⧸ Gamma)]

/-- The explicit distance cutoff has zero mean for the actual original
observation under its invariant probability; integrability is also proved. -/
theorem original_boundary_cutoff_mean_zero
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma)
    (hc : Measurable c.representative)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsProbabilityMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu]
    (S : Set (G ⧸ Gamma)) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => (boundaryCutoff S t (observationQuotientBaseProjection V Gamma x) : ℂ) *
      quotientObservation V c x) mu ∧
    (∫ x, (boundaryCutoff S t (observationQuotientBaseProjection V Gamma x) : ℂ) *
      quotientObservation V c x ∂mu) = 0 := by
  apply quotient_observation_measurable_cutoff_integral_zero V hcont h1 c hc mu
    (fun z => (boundaryCutoff S t z : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      (boundary_cutoff_lipschitz S ht).continuous.measurable) 1
  intro z
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (boundary_cutoff_bounds S t z).2.2.1]
  exact (boundary_cutoff_bounds S t z).2.2.2

variable [PseudoMetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]
  {I : Type*} [Fintype I]

/-- Boundary control of the full original orbit with its exact section and
actual base projection. F43 supplies the measure-preserving premise under
the original invariant-probability and lattice hypotheses. -/
theorem original_boundary_orbit_bound
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma)
    (hc : Measurable c.representative)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsProbabilityMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu]
    (nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure nu]
    (hp : MeasurePreserving (observationQuotientBaseProjection V Gamma) mu nu)
    (J : ℝ≥0) (hJ : LipschitzWith J (observationQuotientBaseProjection V Gamma))
    (S : Set (G ⧸ Gamma)) {t : ℝ} (ht : 0 < t) (K : ℝ≥0)
    (hK : LipschitzWith K (fun x =>
      (boundaryCutoff S t (observationQuotientBaseProjection V Gamma x) : ℂ) * quotientObservation V c x))
    (u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) (alpha : ℝ)
    (heq : LipschitzOrbitDiscrepancy mu u alpha) :
    ‖complexUniformMean (fun i => quotientObservation V c (u i))‖ ≤
      (nu (boundaryTube S (2 * t))).toReal + alpha * (2 + K + t⁻¹ * J) := by
  exact boundary_orbit_observation_bound mu nu (observationQuotientBaseProjection V Gamma) hp J hJ
    S ht (quotientObservation V c) (quotient_observation_norm V c) K hK
    (original_boundary_cutoff_mean_zero V Gamma hcont h1 c hc mu S ht).2 u alpha heq

/-- Fixed structural geometric constants give one positive discrepancy
tolerance before every original orbit, without a zero-mean assumption. -/
theorem original_boundary_nonequidistribution
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma)
    (hc : Measurable c.representative)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsProbabilityMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu]
    (nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure nu]
    (hp : MeasurePreserving (observationQuotientBaseProjection V Gamma) mu nu)
    (J : ℝ≥0) (hJ : LipschitzWith J (observationQuotientBaseProjection V Gamma))
    (S : Set (G ⧸ Gamma)) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hmass : ∀ t : ℝ, 0 < t → t ≤ 1 → (nu (boundaryTube S (2 * t))).toReal ≤ C * t)
    (hK : ∀ t : ℝ, 0 < t → t ≤ 1 → LipschitzWith (Real.toNNReal (A / t)) (fun x =>
      (boundaryCutoff S t (observationQuotientBaseProjection V Gamma x) : ℂ) * quotientObservation V c x))
    (gamma : ℝ) (hg : 0 < gamma) :
    ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
      ∀ (I : Type*) [Fintype I] (u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
        gamma < ‖complexUniformMean (fun i => quotientObservation V c (u i))‖ →
        ¬ LipschitzOrbitDiscrepancy mu u alpha := by
  exact uniform_boundary_nonequidistribution mu nu (observationQuotientBaseProjection V Gamma) hp J hJ
    S (quotientObservation V c) (quotient_observation_norm V c) C A hC hA hmass hK
    (fun t ht _ => (original_boundary_cutoff_mean_zero V Gamma hcont h1 c hc mu S ht).2) gamma hg

end GMZP0
