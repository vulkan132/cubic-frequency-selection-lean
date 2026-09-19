import GMZP0.ObservationMeasurability
import GMZP0.ObservationBoundedSection
import GMZP0.ObservationLatticeCocompact

/-! The actual observation quotient has its Borel quotient structure.
The finite-dimensional function topology is used throughout, and strict
Borel domains are constructed without claiming controlled smooth boundaries. -/
noncomputable section
open Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
/-- The actual finite-dimensional observation space is Polish in its pointwise subspace topology. -/
theorem observation_space_polish (V : ObservationModule G) [FiniteDimensional ℝ V.space] :
    PolishSpace V.space :=
  (Module.finBasis ℝ V.space).equivFun.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.polishSpace

/-- The original product topology on H is Polish when the base is Polish. -/
theorem observation_group_polish [PolishSpace G] (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] : PolishSpace (ObservationGroup V) := by
  let := observation_space_polish V
  exact (observationPairHomeomorph V).isClosedEmbedding.polishSpace

/-- Finite dimension and local compactness of the base imply local compactness of the original H. -/
theorem observation_group_locallyCompact [LocallyCompactSpace G] (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] : LocallyCompactSpace (ObservationGroup V) := by
  let := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ V.space
  exact (observationPairHomeomorph V).isOpenEmbedding.locallyCompactSpace

/-- A Hausdorff base gives the original H a Hausdorff topology. -/
theorem observation_group_t2 [T2Space G] (V : ObservationModule G) : T2Space (ObservationGroup V) :=
  (observationPairHomeomorph V).symm.t2Space

/-- Under the original discrete-lattice hypotheses, the measurable quotient is the Borel quotient.
Normality of Gamma_H is not used. -/
theorem observation_quotient_borel [IsTopologicalGroup G] [PolishSpace G]
    (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [DiscreteTopology (observationIntegerLattice V Gamma)] :
    T2Space (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) ∧
      BorelSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := by
  let := observation_group_polish V
  let := observation_isTopologicalGroup V hcont
  let := observation_group_lattice_discrete V Gamma
  let : IsClosed (observationLatticeSubgroup V Gamma : Set (ObservationGroup V)) :=
    Subgroup.isClosed_of_discrete
  let : T2Space (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := inferInstance
  exact ⟨inferInstance, CosetSpace.borelSpace⟩

/-- The full literal rational presentation supplies a Borel quotient and an actual strict
Borel fundamental domain in H with compact closure. No new domain hypothesis is inserted. -/
theorem observation_borel_domain_of_presentation [IsTopologicalGroup G] [PolishSpace G]
    [LocallyCompactSpace G] (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)]
    {sigma iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space)
    (coord : G → sigma → ℝ) (hc : Continuous coord)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    BorelSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) ∧
      ∃ S : Set (ObservationGroup V), MeasurableSet S ∧ IsCompact (closure S) ∧
        ∀ a : ObservationGroup V, ∃! l : observationLatticeSubgroup V Gamma, a * l ∈ S := by
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
  exact ⟨(observation_quotient_borel V hcont Gamma).2,
    observation_borel_fundamental_domain_exists (observationLatticeSubgroup V Gamma)⟩

end GMZP0
