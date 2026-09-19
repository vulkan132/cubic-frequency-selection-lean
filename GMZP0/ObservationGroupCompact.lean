import GMZP0.ObservationCompactCell
import GMZP0.ObservationTopology

/-! Compactness of the actual observation quotient by right lattice multiplication.
Reduction first changes the base by a right lattice element, retaining the
corresponding pullback, and then rounds the actual translated observation. -/
noncomputable section
open Module
namespace GMZP0
variable {G iota : Type*} [Group G] [TopologicalSpace G]

/-- The observation group's topology is exactly the original product topology. -/
def observationPairHomeomorph (V : ObservationModule G) : ObservationGroup V ≃ₜ G × V.space where
  toFun a := (a.base, a.obs)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := observation_pair_coordinates_continuous V
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- The actual lattice has the product topology of the original base lattice and integer fiber. -/
def observationLatticePairHomeomorph (V : ObservationModule G) (Gamma : Subgroup G) :
    observationLatticeSubgroup V Gamma ≃ₜ Gamma × observationIntegerLattice V Gamma where
  toFun a := (⟨a.val.base, a.property.1⟩, ⟨a.val.obs, a.property.2⟩)
  invFun z := ⟨⟨z.1.val, z.2.val⟩, z.1.property, z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact ((observation_pair_coordinates_continuous V).fst.comp continuous_subtype_val).subtype_mk _
    · exact ((observation_pair_coordinates_continuous V).snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)

/-- Base and fiber discreteness prove discreteness of the actual observation lattice. -/
theorem observation_group_lattice_discrete (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [DiscreteTopology (observationIntegerLattice V Gamma)] :
    DiscreteTopology (observationLatticeSubgroup V Gamma) :=
  (observationLatticePairHomeomorph V Gamma).symm.discreteTopology

/-- A compact product covering cell, retaining the actual pair coordinates. -/
def observationGroupClosedCell [Fintype iota] (V : ObservationModule G)
    (K : Set G) (b : Basis iota ℝ V.space) : Set (ObservationGroup V) :=
  {a | a.base ∈ K ∧ a.obs ∈ observationClosedCell V b}

/-- The original pair cell is compact in the observation group's actual topology. -/
theorem observation_group_closedCell_compact [Fintype iota] (V : ObservationModule G)
    (K : Set G) (hK : IsCompact K) (b : Basis iota ℝ V.space) :
    IsCompact (observationGroupClosedCell V K b) := by
  have he : observationGroupClosedCell V K b =
      (observationPairHomeomorph V).symm '' (K ×ˢ observationClosedCell V b) := by
    ext a
    constructor
    · intro h
      exact ⟨(a.base, a.obs), h, rfl⟩
    · rintro ⟨⟨g, P⟩, h, rfl⟩
      exact h
  rw [he]
  exact (hK.prod (observation_closedCell_compact V b)).image
    (observationPairHomeomorph V).symm.continuous

omit [TopologicalSpace G] in
/-- Right reduction keeps the base correction's pullback before subtracting a genuine integer observation. -/
theorem observation_right_lattice_reduction [Fintype iota] (V : ObservationModule G)
    (Gamma : Subgroup G) (K : Set G)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) (a : ObservationGroup V) :
    ∃ l : observationLatticeSubgroup V Gamma, a * l.val ∈ observationGroupClosedCell V K bR := by
  obtain ⟨gamma, hgamma⟩ := hcover a.base
  obtain ⟨Z, hZ⟩ := observation_reduce_to_closedCell V Gamma bZ bR hb
    (observationTranslate V gamma a.obs)
  let l : observationLatticeSubgroup V Gamma :=
    ⟨⟨gamma, -Z.val⟩, gamma.property, (observationIntegerFunctions V Gamma).neg_mem Z.property⟩
  refine ⟨l, hgamma, ?_⟩
  change observationTranslate V gamma a.obs + -Z.val ∈ observationClosedCell V bR
  simpa only [sub_eq_add_neg] using hZ

/-- A compact base covering set and the actual integer basis prove compactness of H/Gamma_H.
The quotient identifies a with a * l for l in Gamma_H and does not assume normality. -/
theorem observation_group_quotient_compact [Fintype iota] (V : ObservationModule G)
    (Gamma : Subgroup G) (K : Set G) (hK : IsCompact K)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) :
    CompactSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) := by
  let pi : ObservationGroup V → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma :=
    QuotientGroup.mk
  have hsur : pi '' observationGroupClosedCell V K bR = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      obtain ⟨l, hl⟩ := observation_right_lattice_reduction V Gamma K hcover bZ bR hb a
      exact ⟨a * l.val, hl, QuotientGroup.mk_mul_of_mem a l.property⟩
  apply isCompact_univ_iff.mp
  rw [← hsur]
  exact (observation_group_closedCell_compact V K hK bR).image QuotientGroup.continuous_mk

end GMZP0
