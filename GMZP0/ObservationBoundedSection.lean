import GMZP0.ObservationMeasurableSection
import GMZP0.CompactQuotientCover

/-! Compactly contained Borel sections of the actual discrete quotient.
The countable lattice correction is selected by its first successful index.
The resulting domain is strict and Borel, without any smooth-face claim. -/
noncomputable section
open Set Topology
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G]

omit [T2Space G] in
/-- Measurably reduce an existing original section into a supplied Borel covering set. -/
theorem observation_measurable_section_in_cover (Gamma : Subgroup G) [Countable Gamma]
    (c : ObservationSection Gamma) (hc : Measurable c.representative)
    (K : Set G) (hK : MeasurableSet K) (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K) :
    ∃ d : ObservationSection Gamma, Measurable d.representative ∧ Set.range d.representative ⊆ K := by
  classical
  obtain ⟨index, hindex⟩ := exists_surjective_nat Gamma
  have hex (g : G) : ∃ n : ℕ, g * index n ∈ K := by
    obtain ⟨gamma, hgamma⟩ := hcover g
    obtain ⟨n, rfl⟩ := hindex gamma
    exact ⟨n, hgamma⟩
  let R (g : G) := g * index (Nat.find (hex g))
  have hR : Measurable R := Measurable.find
    (f := fun n (g : G) => g * (index n : G))
    (p := fun n (g : G) => g * (index n : G) ∈ K)
    (fun n => measurable_id.mul_const (index n : G))
    (fun n => hK.preimage (measurable_id.mul_const (index n : G))) hex
  have hRK (g : G) : R g ∈ K := Nat.find_spec (hex g)
  let d : ObservationSection Gamma :=
    { representative := fun g => R (c.representative g)
      right_invariant := by intro g gamma; rw [c.right_invariant]
      correction_mem := by
        intro g
        change g⁻¹ * (c.representative g * index (Nat.find (hex (c.representative g)))) ∈ Gamma
        rw [← mul_assoc]
        exact Gamma.mul_mem (c.correction_mem g) (index _).property }
  refine ⟨d, hR.comp hc, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact hRK _

/-- A discrete cocompact subgroup of a locally compact Polish group has a compactly contained Borel section. -/
theorem observation_compact_measurable_section_exists [PolishSpace G] [LocallyCompactSpace G]
    (Gamma : Subgroup G) [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] :
    ∃ (K : Set G) (c : ObservationSection Gamma), IsCompact K ∧
      Measurable c.representative ∧ Set.range c.representative ⊆ K := by
  let : Countable Gamma := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨c, hc⟩ := observation_measurable_section_exists_polish Gamma
  obtain ⟨K, hK, hcover⟩ := compact_quotient_right_cover Gamma
  obtain ⟨d, hd, hdK⟩ := observation_measurable_section_in_cover Gamma c hc K hK.measurableSet hcover
  exact ⟨K, d, hK, hd, hdK⟩

/-- The original quotient has a strict Borel fundamental domain with compact closure.
Right corrections are unique pointwise, including the chosen boundary representatives. -/
theorem observation_borel_fundamental_domain_exists [PolishSpace G] [LocallyCompactSpace G]
    (Gamma : Subgroup G) [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] :
    ∃ S : Set G, MeasurableSet S ∧ IsCompact (closure S) ∧
      ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S := by
  obtain ⟨K, c, hK, hc, hsub⟩ := observation_compact_measurable_section_exists Gamma
  refine ⟨Set.range c.representative, observation_section_measurable_range c hc,
    hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed), ?_⟩
  exact observation_section_unique_correction c

end GMZP0
