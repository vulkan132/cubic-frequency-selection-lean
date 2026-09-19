import GMZP0.ObservationMeasurableSection
import GMZP0.ObservationCutoffIntegral
import GMZP0.ObservationTopology

/-! Measurability of the original observation from the original measurable
section. Its correction and evaluation remain unchanged. These statements
do not replace the specified section by the independently constructed one. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Borel measurable structure of the original observation group's product topology. -/
instance observationGroupMeasurableSpace (V : ObservationModule G) :
    MeasurableSpace (ObservationGroup V) := borel _

instance observationGroupBorelSpace (V : ObservationModule G) :
    BorelSpace (ObservationGroup V) := ⟨rfl⟩

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- The original real phase is measurable with its actual variable lattice correction. -/
theorem observation_real_phase_measurable (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    {Gamma : Subgroup G} (c : ObservationSection Gamma) (hc : Measurable c.representative) :
    Measurable (observationRealPhase V c) := by
  let : MeasurableSpace V.space := borel _
  let : BorelSpace V.space := ⟨rfl⟩
  exact (observation_evaluation_continuous V hcont).measurable.comp
    ((observation_pair_coordinates_continuous V).snd.measurable.prodMk
      ((observation_correction_measurable c hc).comp
        (observation_pair_coordinates_continuous V).fst.measurable))

/-- The original complex observation is measurable on the actual measurable quotient. -/
theorem quotient_observation_measurable (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    {Gamma : Subgroup G} (c : ObservationSection Gamma) (hc : Measurable c.representative) :
    Measurable (quotientObservation V c) := by
  apply QuotientGroup.measurable_from_quotient.mpr
  exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).measurable.comp
    (QuotientAddGroup.continuous_mk.measurable.comp (observation_real_phase_measurable V hcont c hc))

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
/-- The original base-coset projection is measurable. -/
theorem observation_quotient_base_measurable (V : ObservationModule G) (Gamma : Subgroup G) :
    Measurable (observationQuotientBaseProjection V Gamma) := by
  apply QuotientGroup.measurable_from_quotient.mpr
  exact QuotientGroup.measurable_coe.comp (observation_pair_coordinates_continuous V).fst.measurable

/-- A measurable original base cutoff yields a measurable original cutoff observation. -/
theorem quotient_observation_cutoff_measurable (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    {Gamma : Subgroup G} (c : ObservationSection Gamma) (hc : Measurable c.representative)
    (chi : G ⧸ Gamma → ℂ) (hchi : Measurable chi) :
    Measurable (fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) :=
  (hchi.comp (observation_quotient_base_measurable V Gamma)).mul
    (quotient_observation_measurable V hcont c hc)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- The actual quotient action is measurable from the proved original topological group structure. -/
theorem observation_quotient_measurable_action (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) (Gamma : Subgroup G) :
    MeasurableConstSMul (ObservationGroup V)
      (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := by
  let : IsTopologicalGroup (ObservationGroup V) := observation_isTopologicalGroup V hcont
  constructor
  intro a
  apply QuotientGroup.measurable_from_quotient.mpr
  exact QuotientGroup.measurable_coe.comp (continuous_const_mul a).measurable

/-- Discharge the global cutoff's strong measurability premise using the actual section.
The invariant finite measure remains an explicit input. -/
theorem quotient_observation_measurable_cutoff_integral_zero (V : ObservationModule G)
    [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    {Gamma : Subgroup G}
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma)
    (hc : Measurable c.representative)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsFiniteMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu]
    (chi : G ⧸ Gamma → ℂ) (hchi : Measurable chi) (C : ℝ) (hC : ∀ z, ‖chi z‖ ≤ C) :
    Integrable (fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) mu ∧
      (∫ x, chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x ∂mu) = 0 := by
  let := observation_quotient_measurable_action V hcont Gamma
  exact quotient_observation_cutoff_integral_zero V h1 c mu chi C hC
    (quotient_observation_cutoff_measurable V hcont c hc chi hchi).aestronglyMeasurable

end GMZP0
