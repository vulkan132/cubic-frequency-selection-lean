import GMZP0.MeasurableCompactSection
import GMZP0.ObservationQuotient
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Measurable original base sections and their strict Borel fundamental
domains. Existence uses the actual discrete quotient and compactness;
piecewise smooth boundaries and quantitative chart estimates are separate. -/
noncomputable section
open Set Topology
namespace GMZP0
variable {G : Type*} [Group G]

/-- Every original algebraic section fixes its chosen representatives. -/
theorem observation_section_idempotent {Gamma : Subgroup G} (c : ObservationSection Gamma) (g : G) :
    c.representative (c.representative g) = c.representative g := by
  calc
    c.representative (c.representative g) = c.representative (g * observationCorrection c g) :=
      congrArg c.representative (observation_representative_eq c g).symm
    _ = c.representative g := c.right_invariant g (observationCorrection c g)

/-- A section's original range is exactly its fixed-point set. -/
theorem observation_section_range_fixed {Gamma : Subgroup G} (c : ObservationSection Gamma) :
    Set.range c.representative = {g | c.representative g = g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact observation_section_idempotent c u
  · intro h
    exact ⟨g, h⟩

/-- Every point has a unique actual right lattice correction into the section's range. -/
theorem observation_section_unique_correction {Gamma : Subgroup G} (c : ObservationSection Gamma)
    (g : G) : ∃! gamma : Gamma, g * gamma ∈ Set.range c.representative := by
  refine ⟨observationCorrection c g, ?_, ?_⟩
  · change g * observationCorrection c g ∈ Set.range c.representative
    rw [observation_representative_eq]
    exact ⟨g, rfl⟩
  · intro gamma hgamma
    have hfix : c.representative (g * gamma) = g * gamma := by
      change g * gamma ∈ {u | c.representative u = u}
      rw [← observation_section_range_fixed c]
      exact hgamma
    rw [c.right_invariant] at hfix
    apply Subtype.ext
    apply mul_left_cancel (a := g)
    rw [observation_representative_eq]
    exact hfix.symm

section Measurable
variable [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A measurable original section has a Borel set of representatives. -/
theorem observation_section_measurable_range [T2Space G] [SecondCountableTopology G]
    {Gamma : Subgroup G} (c : ObservationSection Gamma)
    (hc : Measurable c.representative) : MeasurableSet (Set.range c.representative) := by
  rw [observation_section_range_fixed]
  exact measurableSet_eq_fun hc measurable_id

variable [IsTopologicalGroup G]

/-- The actual correction g^{-1}*c(g) is measurable whenever the original section is measurable. -/
theorem observation_correction_measurable [SecondCountableTopology G]
    {Gamma : Subgroup G} (c : ObservationSection Gamma)
    (hc : Measurable c.representative) :
    Measurable (fun g => (observationCorrection c g : G)) :=
  measurable_id.inv.mul hc

/-- A compact quotient by a discrete subgroup admits a genuine measurable original section.
Normality, a continuous global section, and smooth boundary data are not assumed. -/
theorem observation_measurable_section_exists (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] [BorelSpace (G ⧸ Gamma)] :
    ∃ c : ObservationSection Gamma, Measurable c.representative := by
  obtain ⟨s, hs, hright⟩ := compact_local_homeomorph_measurable_section
    (QuotientGroup.mk : G → G ⧸ Gamma)
    (Gamma.isQuotientCoveringMap (isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap.isLocalHomeomorph
    QuotientGroup.mk_surjective
  let c : ObservationSection Gamma :=
    { representative := fun g => s (QuotientGroup.mk g)
      right_invariant := by
        intro g gamma
        rw [QuotientGroup.mk_mul_of_mem g gamma.property]
      correction_mem := by
        intro g
        exact QuotientGroup.eq.mp (hright (QuotientGroup.mk g)).symm }
  exact ⟨c, hs.comp QuotientGroup.measurable_coe⟩

/-- For a Polish base, the actual quotient's Borel structure follows from discreteness internally. -/
theorem observation_measurable_section_exists_polish [PolishSpace G] (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] :
    ∃ c : ObservationSection Gamma, Measurable c.representative := by
  let : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  let : T2Space (G ⧸ Gamma) := inferInstance
  let : BorelSpace (G ⧸ Gamma) := CosetSpace.borelSpace
  exact observation_measurable_section_exists Gamma

end Measurable
end GMZP0
