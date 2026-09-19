import GMZP0.TriangularIntegerCell
import GMZP0.ObservationBoundedSection
import Mathlib.Topology.Order.Compact

/-! The actual half-open coordinate domain from triangular group laws.
Its unique original lattice corrections identify every specified section
whose representatives lie in this domain. -/
noncomputable section
open Set TopologicalSpace
namespace GMZP0
variable {G : Type*} [Group G] {m : ℕ}

/-- A fixed translated half-open unit cell in the actual coordinates. -/
def coordinateHalfOpenCell (coord : G → Fin m → ℝ) (a : Fin m → ℝ) : Set G :=
  {g | ∀ i, coord g i ∈ Set.Ico (a i) (a i + 1)}

/-- Literal triangular group laws and the complete original integer grid give unique right corrections. -/
theorem triangular_coordinate_cell_correction (Gamma : Subgroup G)
    (coord : G → Fin m → ℝ) (hinj : Function.Injective coord)
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) (g : G) :
    ∃! gamma : Gamma, g * gamma ∈ coordinateHalfOpenCell coord a := by
  obtain ⟨z, hz, huniq⟩ := triangular_integer_cell
    (fun i u => MvPolynomial.aeval u (q g i)) a
    (fun i u v huv => polynomial_eval_eq_of_prefix i (q g i) (hlow g i) u v huv)
  obtain ⟨gamma, hgamma⟩ := hcover z
  refine ⟨gamma, ?_, ?_⟩
  · intro i
    rw [hcoord, hgamma]
    exact hz i
  · intro delta hdelta
    obtain ⟨w, hw⟩ := hint delta
    have hwcell : ∀ i, (w i : ℝ) + MvPolynomial.aeval (fun j => (w j : ℝ)) (q g i) ∈
        Set.Ico (a i) (a i + 1) := by
      intro i
      have h := hdelta i
      rwa [hcoord, hw] at h
    have he : w = z := huniq w hwcell
    apply Subtype.ext
    apply hinj
    rw [hw, hgamma, he]

/-- Any two sections in the same strict original right-correction domain coincide pointwise. -/
theorem observation_sections_eq_on_strict_domain (Gamma : Subgroup G) (S : Set G)
    (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S)
    (c d : ObservationSection Gamma)
    (hc : Set.range c.representative ⊆ S) (hd : Set.range d.representative ⊆ S) :
    c.representative = d.representative := by
  funext g
  have hc' : g * observationCorrection c g ∈ S := by
    rw [observation_representative_eq]
    exact hc ⟨g, rfl⟩
  have hd' : g * observationCorrection d g ∈ S := by
    rw [observation_representative_eq]
    exact hd ⟨g, rfl⟩
  have he := (hunique g).unique hc' hd'
  rw [← observation_representative_eq c g, ← observation_representative_eq d g, he]

section Topology
variable [TopologicalSpace G]

omit [Group G] in
/-- The half-open coordinate cell is Borel in the original topology. -/
theorem coordinate_half_open_cell_measurable [MeasurableSpace G] [BorelSpace G]
    (coord : G → Fin m → ℝ) (hc : Continuous coord) (a : Fin m → ℝ) :
    MeasurableSet (coordinateHalfOpenCell coord a) := by
  convert MeasurableSet.iInter (fun i : Fin m => (measurableSet_Ico : MeasurableSet (Set.Ico (a i) (a i + 1))).preimage
    ((continuous_apply i).comp hc).measurable) using 1
  ext g
  simp [coordinateHalfOpenCell]

omit [Group G] in
/-- A genuine coordinate homeomorphism gives the half-open cell compact closure. -/
theorem coordinate_half_open_cell_compact_closure (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    IsCompact (closure (coordinateHalfOpenCell coord a)) := by
  let : T2Space G := coord.symm.t2Space
  let K := coord.symm '' Set.Icc a (fun i => a i + 1)
  have hK : IsCompact K := isCompact_Icc.image coord.symm.continuous
  have hsub : coordinateHalfOpenCell coord a ⊆ K := by
    intro g hg
    exact ⟨coord g, ⟨fun i => (hg i).1, fun i => (hg i).2.le⟩, coord.symm_apply_apply g⟩
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

/-- A compactly contained exact right-correction domain makes the original quotient compact. -/
theorem quotient_compact_of_strict_cell [IsTopologicalGroup G] (Gamma : Subgroup G)
    (S : Set G) (hS : IsCompact (closure S))
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ S) : CompactSpace (G ⧸ Gamma) := by
  have himage : (QuotientGroup.mk : G → G ⧸ Gamma) '' closure S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨gamma, hgamma⟩ := hcover g
    exact ⟨g * gamma, subset_closure hgamma, QuotientGroup.mk_mul_of_mem g gamma.property⟩
  exact ⟨by simpa only [himage] using hS.image (QuotientGroup.continuous_mk (N := Gamma))⟩

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [PolishSpace G]

/-- A strict Borel right-correction domain has one measurable section, agreeing with every specified one in it. -/
theorem measurable_section_of_strict_domain (Gamma : Subgroup G) [DiscreteTopology Gamma]
    [CompactSpace (G ⧸ Gamma)] (S : Set G) (hS : MeasurableSet S)
    (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S) :
    ∃ d : ObservationSection Gamma, Measurable d.representative ∧ Set.range d.representative ⊆ S ∧
      ∀ c : ObservationSection Gamma, Set.range c.representative ⊆ S → c.representative = d.representative := by
  let : Countable Gamma := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨c0, hc0⟩ := observation_measurable_section_exists_polish Gamma
  obtain ⟨d, hd, hdS⟩ := observation_measurable_section_in_cover Gamma c0 hc0 S hS
    (fun g => (hunique g).exists)
  exact ⟨d, hd, hdS, fun c hc => observation_sections_eq_on_strict_domain Gamma S hunique c d hc hdS⟩

/-- The specified original section is measurable when it takes its values in the proved strict Borel domain. -/
theorem specified_section_measurable_of_strict_domain (Gamma : Subgroup G) [DiscreteTopology Gamma]
    [CompactSpace (G ⧸ Gamma)] (S : Set G) (hS : MeasurableSet S)
    (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ S) :
    Measurable c.representative := by
  obtain ⟨d, hd, _, he⟩ := measurable_section_of_strict_domain Gamma S hS hunique
  rw [he c hc]
  exact hd

end Topology
end GMZP0
