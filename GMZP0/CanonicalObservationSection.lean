import GMZP0.CanonicalCoordinateCell
import GMZP0.ObservationGlobalMean

/-! Match the specified original section to its actual triangular coordinate
cell. No new representative is substituted in the original observation.
The cell is a translated half-open unit box; more general chosen domains
and quantitative face neighborhoods require separate arguments. -/
noncomputable section
open Set Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {m : ℕ}

/-- The literal coordinate laws construct the canonical cell section and the actual compact quotient. -/
theorem canonical_coordinate_section (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ)) (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) :
    CompactSpace (G ⧸ Gamma) ∧ IsCompact (closure (coordinateHalfOpenCell coord a)) ∧
      ∃ d : ObservationSection Gamma, Measurable d.representative ∧
        Set.range d.representative ⊆ coordinateHalfOpenCell coord a ∧
        ∀ c : ObservationSection Gamma, Set.range c.representative ⊆ coordinateHalfOpenCell coord a →
          c.representative = d.representative := by
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q hcoord hlow hint hcover a
  have hK := coordinate_half_open_cell_compact_closure coord a
  let : CompactSpace (G ⧸ Gamma) := quotient_compact_of_strict_cell Gamma _ hK (fun g => (huniq g).exists)
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  exact ⟨inferInstance, hK, measurable_section_of_strict_domain Gamma _
    (coordinate_half_open_cell_measurable coord coord.continuous a) huniq⟩

/-- A specified original section in this exact coordinate cell is measurable by pointwise identification. -/
theorem specified_canonical_coordinate_section_measurable (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ)) (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) (c : ObservationSection Gamma)
    (hc : Set.range c.representative ⊆ coordinateHalfOpenCell coord a) : Measurable c.representative := by
  obtain ⟨_, _, d, hd, _, he⟩ := canonical_coordinate_section Gamma coord q hcoord hlow hint hcover a
  rw [he c hc]
  exact hd

/-- The original mean-zero result now follows for every specified section in the actual coordinate cell.
Base Polish/local compactness, quotient compactness and section measurability are derived internally. -/
theorem canonical_original_observation_mean_zero
    (V : ObservationModule G) (Gamma : Subgroup G) [DiscreteTopology Gamma]
    {iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space)
    (coord : G ≃ₜ (Fin m → ℝ)) (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (a : Fin m → ℝ) :
    ∃ mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
      IsProbabilityMeasure mu ∧
      SMulInvariantMeasure (ObservationGroup V) (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) mu ∧
      ∀ c : ObservationSection Gamma, Set.range c.representative ⊆ coordinateHalfOpenCell coord a →
      ∀ chi : G ⧸ Gamma → ℂ, Measurable chi →
      ∀ C : ℝ, (∀ z, ‖chi z‖ ≤ C) →
        Integrable (fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) mu ∧
        (∫ x, chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x ∂mu) = 0 := by
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  let : CompactSpace (G ⧸ Gamma) := (canonical_coordinate_section Gamma coord q hcoord hlow hint hcover a).1
  obtain ⟨mu, hprob, hinv, hmean⟩ := observation_global_mean_zero_of_presentation
    V Gamma b coord coord.continuous hint hcover P hb h1
  refine ⟨mu, hprob, hinv, ?_⟩
  intro c hc
  exact hmean c (specified_canonical_coordinate_section_measurable Gamma coord q hcoord hlow hint hcover a c hc)

end GMZP0
