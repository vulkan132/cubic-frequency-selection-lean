import GMZP0.CanonicalSectionContinuity
import GMZP0.QuotientBoundaryTube
import Mathlib.Topology.LocallyConstant.Basic

/-! Finiteness of the original lattice corrections in compact charts and
the exact boundary crossed when an original correction changes. -/
noncomputable section
open Set Filter Topology Metric
open scoped Pointwise
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compact input and representative sets give finitely many actual right
corrections. No continuity of the chosen original section is required. -/
theorem original_corrections_finite_on_compact [T2Space G]
    (Gamma : Subgroup G) [DiscreteTopology Gamma] (c : ObservationSection Gamma)
    (K D : Set G) (hK : IsCompact K) (hD : IsCompact D)
    (hc : Set.range c.representative ⊆ D) :
    (observationCorrection c '' K).Finite := by
  have hclosed : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  have hfinite : (Subtype.val ⁻¹' (K⁻¹ * D) : Set Gamma).Finite :=
    (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hD)).finite_of_discrete
  apply hfinite.subset
  rintro gamma ⟨g, hg, rfl⟩
  exact ⟨g⁻¹, by simpa using hg, c.representative g, hc ⟨g, rfl⟩, rfl⟩

omit [IsTopologicalGroup G] in
/-- Avoiding the actual quotient image of the frontier forces the original
representative into the interior of its specified domain. -/
theorem original_representative_interior_off_faces
    (Gamma : Subgroup G) (D : Set G) (c : ObservationSection Gamma)
    (hc : Set.range c.representative ⊆ D) (g : G)
    (hg : (QuotientGroup.mk g : G ⧸ Gamma) ∉ QuotientGroup.mk '' frontier D) :
    c.representative g ∈ interior D := by
  by_contra h
  apply hg
  refine ⟨c.representative g, ⟨subset_closure (hc ⟨g, rfl⟩), h⟩, ?_⟩
  exact (QuotientGroup.eq.mpr (c.correction_mem g)).symm

/-- On any connected parameter space, a continuous base path avoiding all
original quotient faces retains exactly one original lattice correction. -/
theorem original_correction_constant_off_faces
    (Gamma : Subgroup G) (D : Set G)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (p : X → G) (hp : Continuous p)
    (havoid : ∀ x, (QuotientGroup.mk (p x) : G ⧸ Gamma) ∉ QuotientGroup.mk '' frontier D)
    (x y : X) : observationCorrection c (p x) = observationCorrection c (p y) := by
  have hloc : IsLocallyConstant (fun z => observationCorrection c (p z)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact (original_correction_locally_constant Gamma D huniq c hc (p z)
      (original_representative_interior_off_faces Gamma D c hc (p z) (havoid z))).comp_tendsto
      hp.continuousAt
  exact hloc.apply_eq_of_preconnectedSpace x y

/-- If two original corrections differ, every continuous connected path
between their base points meets the actual quotient face image. -/
theorem original_correction_change_crosses_faces
    (Gamma : Subgroup G) (D : Set G)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (p : X → G) (hp : Continuous p) (x y : X)
    (hne : observationCorrection c (p x) ≠ observationCorrection c (p y)) :
    ∃ z : X, (QuotientGroup.mk (p z) : G ⧸ Gamma) ∈ QuotientGroup.mk '' frontier D := by
  by_contra h
  push Not at h
  exact hne (original_correction_constant_off_faces Gamma D huniq c hc p hp h x y)

variable (Gamma : Subgroup G) [PseudoMetricSpace (G ⧸ Gamma)]

/-- A bounded connected path converts a genuine correction change into a
quantitative distance bound to the original boundary. -/
theorem original_correction_change_boundary_distance (D : Set G)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (p : X → G) (hp : Continuous p) (x y : X)
    (hne : observationCorrection c (p x) ≠ observationCorrection c (p y))
    (R : ℝ) (hR : ∀ z, dist (QuotientGroup.mk (p x) : G ⧸ Gamma) (QuotientGroup.mk (p z)) ≤ R) :
    (QuotientGroup.mk '' frontier D : Set (G ⧸ Gamma)).Nonempty ∧
      infDist (QuotientGroup.mk (p x) : G ⧸ Gamma) (QuotientGroup.mk '' frontier D) ≤ R := by
  obtain ⟨z, hz⟩ := original_correction_change_crosses_faces Gamma D huniq c hc p hp x y hne
  exact ⟨⟨_, hz⟩, (infDist_le_dist_of_mem hz).trans (hR z)⟩

end GMZP0
