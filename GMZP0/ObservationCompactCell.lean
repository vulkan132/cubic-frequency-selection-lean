import GMZP0.ObservationQuotientCoordinates
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Group.Quotient

/-! A compact closed covering cell in the original observation space.
Rounding uses a genuine integer basis and retains the exact original lattice correction.
The closed cell may overlap at its boundary; no measure or unique-section claim is made. -/
noncomputable section
open Module
namespace GMZP0
variable {G iota : Type*} [Group G] [Fintype iota]

/-- The closed unit coordinate box transported into the original real observation space. -/
def observationClosedCell (V : ObservationModule G) (b : Basis iota ℝ V.space) : Set V.space :=
  b.equivFun.symm '' Set.Icc (0 : iota → ℝ) 1

/-- Membership means that each actual basis coordinate lies in the closed unit interval. -/
theorem observationClosedCell_mem (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (F : V.space) : F ∈ observationClosedCell V b ↔ ∀ i, b.repr F i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩ i
    have he : b.repr (b.equivFun.symm a) i = a i := by
      change b.equivFun (b.equivFun.symm a) i = a i
      rw [LinearEquiv.apply_symm_apply]
    rw [he]
    exact ⟨ha.1 i, ha.2 i⟩
  · intro h
    refine ⟨b.equivFun F, ⟨fun i => (h i).1, fun i => (h i).2⟩, ?_⟩
    exact b.equivFun.symm_apply_apply F

/-- The closed cell is compact for the original pointwise subspace topology. -/
theorem observation_closedCell_compact (V : ObservationModule G) (b : Basis iota ℝ V.space) :
    IsCompact (observationClosedCell V b) :=
  isCompact_Icc.image b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional

/-- Rounding every real basis coordinate selects an actual integer-valued observation. -/
def observationLatticeRounding (V : ObservationModule G) (Gamma : Subgroup G)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (F : V.space) : observationIntegerLattice V Gamma :=
  ∑ i, (⌊bR.repr F i⌋ : ℤ) • bZ i

/-- The selected original lattice element is precisely the real sum of the rounded coordinates. -/
theorem observation_lattice_rounding_sum (V : ObservationModule G) (Gamma : Subgroup G)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) (F : V.space) :
    (observationLatticeRounding V Gamma bZ bR F).val =
      ∑ i, ((⌊bR.repr F i⌋ : ℤ) : ℝ) • bR i := by
  classical
  change (observationIntegerLattice V Gamma).subtype (∑ i, (⌊bR.repr F i⌋ : ℤ) • bZ i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change (⌊bR.repr F i⌋ : ℤ) • (bZ i).val = _
  rw [← hb]
  exact (Int.cast_smul_eq_zsmul ℝ _ _).symm

/-- The exact real remainder has coordinates in [0,1), with no circle division. -/
theorem observation_lattice_remainder_coordinates (V : ObservationModule G) (Gamma : Subgroup G)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) (F : V.space) (i : iota) :
    bR.repr (F - (observationLatticeRounding V Gamma bZ bR F).val) i ∈ Set.Ico (0 : ℝ) 1 := by
  classical
  have he : bR.repr (F - (observationLatticeRounding V Gamma bZ bR F).val) i =
      bR.repr F i - (⌊bR.repr F i⌋ : ℤ) := by
    rw [observation_lattice_rounding_sum V Gamma bZ bR hb F]
    simp [Finsupp.single_apply]
  rw [he]
  constructor
  · exact sub_nonneg.mpr (Int.floor_le _)
  · have h := Int.lt_floor_add_one (bR.repr F i)
    linarith

/-- Every original observation can be reduced into the compact cell by an actual integer lattice element. -/
theorem observation_reduce_to_closedCell (V : ObservationModule G) (Gamma : Subgroup G)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) (F : V.space) :
    ∃ Z : observationIntegerLattice V Gamma, F - Z.val ∈ observationClosedCell V bR := by
  refine ⟨observationLatticeRounding V Gamma bZ bR F, (observationClosedCell_mem V bR _).mpr ?_⟩
  intro i
  have h := observation_lattice_remainder_coordinates V Gamma bZ bR hb F i
  exact ⟨h.1, h.2.le⟩

/-- The original additive lattice quotient is compact, in its actual quotient topology. -/
theorem observation_integer_quotient_compact (V : ObservationModule G) (Gamma : Subgroup G)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) :
    CompactSpace (V.space ⧸ observationIntegerFunctions V Gamma) := by
  let pi : V.space → V.space ⧸ observationIntegerFunctions V Gamma := QuotientAddGroup.mk
  have hsur : pi '' observationClosedCell V bR = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    induction x using Quotient.inductionOn with
    | h F =>
      obtain ⟨Z, hZ⟩ := observation_reduce_to_closedCell V Gamma bZ bR hb F
      refine ⟨F - Z.val, hZ, ?_⟩
      apply QuotientAddGroup.eq.mpr
      change -(F - Z.val) + F ∈ observationIntegerFunctions V Gamma
      have he : -(F - Z.val) + F = Z.val := by abel
      rw [he]
      exact Z.property
  apply isCompact_univ_iff.mp
  rw [← hsur]
  exact (observation_closedCell_compact V bR).image QuotientAddGroup.continuous_mk

end GMZP0
