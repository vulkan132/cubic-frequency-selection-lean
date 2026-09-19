import GMZP0.QuotientProbabilityUnique
import GMZP0.ObservationGlobalMean
import GMZP0.ObservationCommutator

/-! Identify the actual observation quotient probability and its original
base marginal. The projection retains the original coordinates and full
group action, including for nonnormal lattices. -/
noncomputable section
open Set Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G]

/-- The original base projection intertwines the full observation-group action. -/
theorem observationQuotientBaseProjection_smul (V : ObservationModule G) (Gamma : Subgroup G)
    (a : ObservationGroup V) (x : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) :
    observationQuotientBaseProjection V Gamma (a • x) =
      a.base • observationQuotientBaseProjection V Gamma x := by
  induction x using Quotient.inductionOn with
  | h b => rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The original base marginal of every full-H invariant measure is full-G invariant. -/
theorem observation_base_marginal_invariant (V : ObservationModule G) (Gamma : Subgroup G)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) mu] :
    SMulInvariantMeasure G (G ⧸ Gamma) (mu.map (observationQuotientBaseProjection V Gamma)) := by
  constructor
  intro g A hA
  have hpi := observation_quotient_base_measurable V Gamma
  have hg : Measurable (fun z : G ⧸ Gamma => g • z) := by
    apply QuotientGroup.measurable_from_quotient.mpr
    exact QuotientGroup.measurable_coe.comp (continuous_const_mul g).measurable
  rw [Measure.map_apply hpi (hA.preimage hg), Measure.map_apply hpi hA]
  have he : observationQuotientBaseProjection V Gamma ⁻¹' ((fun z : G ⧸ Gamma => g • z) ⁻¹' A) =
      (fun x => observationBaseInclusion V g • x) ⁻¹' (observationQuotientBaseProjection V Gamma ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage, observationQuotientBaseProjection_smul,
      observation_base_inclusion_base]
  rw [he]
  exact SMulInvariantMeasure.measure_preimage_smul (observationBaseInclusion V g) (hA.preimage hpi)

/-- The original base projection preserves the specified invariant probability measures.
Neither a marginal identity nor normality of the lattices is assumed. -/
theorem observation_base_projection_measurePreserving [PolishSpace G] [LocallyCompactSpace G]
    (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)]
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsProbabilityMeasure mu]
    [SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) mu]
    (nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure nu] [SMulInvariantMeasure G (G ⧸ Gamma) nu] :
    MeasurePreserving (observationQuotientBaseProjection V Gamma) mu nu := by
  have hpi := observation_quotient_base_measurable V Gamma
  let : IsProbabilityMeasure (mu.map (observationQuotientBaseProjection V Gamma)) :=
    Measure.isProbabilityMeasure_map hpi.aemeasurable
  let := observation_base_marginal_invariant V Gamma mu
  exact ⟨hpi, compact_quotient_invariant_probability_unique Gamma _ nu⟩

/-- The literal presentation gives a unique full-H invariant probability and identifies
its marginal with every specified full-G invariant probability on the original base quotient. -/
theorem observation_measure_identification_of_presentation [PolishSpace G] [LocallyCompactSpace G]
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
      SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) mu ∧
      (∀ nu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
        IsProbabilityMeasure nu →
        SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) nu → nu = mu) ∧
      (∀ nu : Measure (G ⧸ Gamma), IsProbabilityMeasure nu → SMulInvariantMeasure G (G ⧸ Gamma) nu →
        MeasurePreserving (observationQuotientBaseProjection V Gamma) mu nu) := by
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
  obtain ⟨mu, hprob, hinv⟩ := observation_quotient_probability_of_presentation V Gamma b coord hc hint hcover P hb
  let := hprob
  let := hinv
  refine ⟨mu, hprob, hinv, ?_, ?_⟩
  · intro nu hp hi
    let := hp
    let := hi
    exact compact_quotient_invariant_probability_unique (observationLatticeSubgroup V Gamma) nu mu
  · intro nu hp hi
    let := hp
    let := hi
    exact observation_base_projection_measurePreserving V Gamma mu nu

end GMZP0
