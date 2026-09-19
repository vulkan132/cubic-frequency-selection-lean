import Mathlib.Topology.Covering.Quotient
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! A measurable section of a surjective local homeomorphism onto a compact
space. The construction uses finitely many local inverses and measurable
selection of the first covering chart; it asserts no boundary regularity. -/
noncomputable section
open Set Topology
namespace GMZP0

/-- A compact target permits a genuine Borel section assembled from local inverses. -/
theorem compact_local_homeomorph_measurable_section
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [Nonempty X] [CompactSpace Y] (f : X → Y) (hf : IsLocalHomeomorph f)
    (hsur : Function.Surjective f) :
    ∃ s : Y → X, Measurable s ∧ Function.RightInverse s f := by
  classical
  have hchart (y : Y) : ∃ e : OpenPartialHomeomorph X Y, y ∈ e.target ∧ f = e := by
    obtain ⟨x, rfl⟩ := hsur y
    obtain ⟨e, hx, he⟩ := hf x
    refine ⟨e, ?_, he⟩
    rw [he]
    exact e.map_source hx
  choose e he hfe using hchart
  have hcov : (Set.univ : Set Y) ⊆ ⋃ y, (e y).target := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, he y⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun y => (e y).target) (fun y => (e y).open_target) hcov
  let x0 : X := Classical.choice inferInstance
  have hSne : Nonempty (↑S : Type _) := by
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ (f x0)))
    obtain ⟨hyS, _⟩ := Set.mem_iUnion.mp hy
    exact ⟨⟨y, hyS⟩⟩
  let := hSne
  obtain ⟨index, hindex⟩ := exists_surjective_nat (↑S : Type _)
  let U (n : ℕ) := (e (index n).val).target
  let localSection (n : ℕ) (y : Y) : X :=
    if _hy : y ∈ U n then (e (index n).val).symm y else x0
  have hU (n : ℕ) : MeasurableSet (U n) := (e (index n).val).open_target.measurableSet
  have hi (n : ℕ) : Measurable (localSection n) := by
    exact ((continuousOn_iff_continuous_domRestrict.mp (e (index n).val).continuousOn_symm).measurable).dite
      (measurable_const : Measurable (fun _ : {y : Y // y ∉ U n} => x0)) (hU n)
  have hex (y : Y) : ∃ n, y ∈ U n := by
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ y))
    obtain ⟨hzS, hy⟩ := Set.mem_iUnion.mp hz
    obtain ⟨n, hn⟩ := hindex ⟨z, hzS⟩
    refine ⟨n, ?_⟩
    simpa only [U, hn] using hy
  refine ⟨fun y => localSection (Nat.find (hex y)) y,
    Measurable.find (p := fun n y => y ∈ U n) hi hU hex, ?_⟩
  intro y
  change f (localSection (Nat.find (hex y)) y) = y
  dsimp only [localSection]
  rw [dif_pos (Nat.find_spec (hex y)), hfe]
  exact (e (index (Nat.find (hex y))).val).right_inv (Nat.find_spec (hex y))

end GMZP0
