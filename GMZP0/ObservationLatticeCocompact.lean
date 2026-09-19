import GMZP0.ObservationGroupCompact
import GMZP0.CompactQuotientCover

/-! Discreteness and cocompactness of the original observation lattice.
All integer and real bases are obtained from the actual rational polynomial
presentation. Base compactness is used through the quotient, without a
global continuous section or normality of either lattice. -/
noncomputable section
open Module
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Compactness of the original base quotient suffices for the observation quotient. -/
theorem observation_group_quotient_compact_of_base [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G) [CompactSpace (G ⧸ Gamma)]
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) :
    CompactSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := by
  obtain ⟨K, hK, hcover⟩ := compact_quotient_right_cover Gamma
  exact observation_group_quotient_compact V Gamma K hK hcover bZ bR hb

/-- The literal rational basis and full integer coordinate grid construct the compact quotient.
No integer basis or compact covering domain is supplied as an extra premise. -/
theorem observation_group_cocompact_of_presentation [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G) [CompactSpace (G ⧸ Gamma)]
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    CompactSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hsep := observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hb)
  have hfull := observation_integer_span_top V Gamma b coord hint P hb
  obtain ⟨d, ⟨bZ⟩⟩ := observation_integer_basis V Gamma hsep
  exact observation_group_quotient_compact_of_base V Gamma bZ
    (observationRealBasis V Gamma bZ hsep hfull)
    (observationRealBasis_apply V Gamma bZ hsep hfull)

/-- The actual rational presentation supplies a topological observation group with discrete
and cocompact original lattice. This is qualitative and does not construct Lie or height data. -/
theorem observation_group_lattice_of_presentation [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)]
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ) (hc : Continuous coord)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    IsTopologicalGroup (ObservationGroup V) ∧
      DiscreteTopology (observationLatticeSubgroup V Gamma) ∧
      CompactSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  let : DiscreteTopology (observationIntegerLattice V Gamma) :=
    (observation_integer_full_lattice V Gamma b coord hint hcover P hb).1
  refine ⟨?_, observation_group_lattice_discrete V Gamma,
    observation_group_cocompact_of_presentation V Gamma b coord hint hcover P hb⟩
  exact observation_isTopologicalGroup V
    (observation_function_continuous_of_coordinates V coord hc
      (observation_representatives_of_rational_basis V b coord P hb))

end GMZP0
