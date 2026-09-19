import GMZP0.CompactQuotientMeasure
import GMZP0.ObservationQuotientBorel

/-! A single invariant probability on the original observation quotient,
and actual zero means for every specified measurable original section.
The ambient Haar invariance and normalization are constructed internally;
the given section and original observation are never replaced. -/
noncomputable section
open Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [PolishSpace G] [LocallyCompactSpace G]

/-- Construct invariant probability on the actual quotient from the literal rational presentation. -/
theorem observation_quotient_probability_of_presentation
    (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)]
    {sigma iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space)
    (coord : G → sigma → ℝ) (hc : Continuous coord)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    ∃ mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
      IsProbabilityMeasure mu ∧
      SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) mu := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hcont := observation_function_continuous_of_coordinates V coord hc
    (observation_representatives_of_rational_basis V b coord P hb)
  let : DiscreteTopology (observationIntegerLattice V Gamma) :=
    (observation_integer_full_lattice V Gamma b coord hint hcover P hb).1
  let := observation_group_polish V
  let := observation_group_locallyCompact V
  let := observation_isTopologicalGroup V hcont
  let := observation_group_lattice_discrete V Gamma
  let := observation_group_cocompact_of_presentation V Gamma b coord hint hcover P hb
  exact compact_quotient_invariant_probability (observationLatticeSubgroup V Gamma)

/-- One probability measure works for every specified measurable original section and every
bounded measurable base cutoff. Integrability and zero mean are both concluded. -/
theorem observation_global_mean_zero_of_presentation [MeasurableSpace G] [BorelSpace G]
    (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)]
    {sigma iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space)
    (coord : G → sigma → ℝ) (hc : Continuous coord)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) :
    ∃ mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
      IsProbabilityMeasure mu ∧
      SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) mu ∧
      ∀ (c : ObservationSection Gamma), Measurable c.representative →
      ∀ (chi : G ⧸ Gamma → ℂ), Measurable chi →
      ∀ C : ℝ, (∀ z, ‖chi z‖ ≤ C) →
        Integrable (fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) mu ∧
        (∫ x, chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x ∂mu) = 0 := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hcont := observation_function_continuous_of_coordinates V coord hc
    (observation_representatives_of_rational_basis V b coord P hb)
  obtain ⟨mu, hprob, hinv⟩ :=
    observation_quotient_probability_of_presentation V Gamma b coord hc hint hcover P hb
  let := hprob
  let := hinv
  refine ⟨mu, hprob, hinv, ?_⟩
  intro c hcm chi hchi C hC
  exact quotient_observation_measurable_cutoff_integral_zero V hcont h1 c hcm mu chi hchi C hC

end GMZP0
