import GMZP0.CanonicalCoordinateCell
import GMZP0.CoordinateBoundaryStrips
import Mathlib.Topology.Order.DenselyOrdered

/-! The actual coordinate cell frontier and its original lattice translates.
Strict right corrections keep all translated frontiers out of the interior. -/
noncomputable section
open Set Topology Metric
namespace GMZP0
variable {G : Type*} [TopologicalSpace G] {m : ℕ}

/-- The closure of the original half-open cell is its closed coordinate box. -/
theorem coordinate_cell_closure (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    closure (coordinateHalfOpenCell coord a) = coord ⁻¹' Set.Icc a (fun i => a i + 1) := by
  have he : coordinateHalfOpenCell coord a =
      coord ⁻¹' Set.pi Set.univ (fun i => Set.Ico (a i) (a i + 1)) := by
    ext g
    simp [coordinateHalfOpenCell, Set.mem_pi]
  rw [he, ← coord.preimage_closure, closure_pi_set]
  have hclose (i : Fin m) : closure (Set.Ico (a i) (a i + 1)) = Set.Icc (a i) (a i + 1) :=
    closure_Ico (by linarith)
  congr 1
  ext u
  simp only [Set.mem_pi, Set.mem_univ, forall_const, hclose, Set.mem_Icc, Pi.le_def]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨hlo, hhi⟩ i
    exact ⟨hlo i, hhi i⟩

/-- Strict inequalities characterize the exact interior in every finite dimension. -/
theorem coordinate_cell_interior (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    interior (coordinateHalfOpenCell coord a) = {g | ∀ i, a i < coord g i ∧ coord g i < a i + 1} := by
  have he : coordinateHalfOpenCell coord a =
      coord ⁻¹' Set.pi Set.univ (fun i => Set.Ico (a i) (a i + 1)) := by
    ext g
    simp [coordinateHalfOpenCell, Set.mem_pi]
  rw [he, ← coord.preimage_interior, interior_pi_set (Set.toFinite Set.univ)]
  ext g
  simp [interior_Ico, Set.mem_pi]

/-- The actual frontier is exactly the preimage of all original coordinate faces. -/
theorem coordinate_cell_frontier (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    frontier (coordinateHalfOpenCell coord a) = coord ⁻¹' coordinateCellFaces a := by
  classical
  rw [frontier, coordinate_cell_closure, coordinate_cell_interior]
  ext g
  constructor
  · intro hg
    refine ⟨hg.1, ?_⟩
    obtain ⟨i, hi⟩ := not_forall.mp hg.2
    rcases not_and_or.mp hi with hi | hi
    · exact ⟨i, Or.inl (le_antisymm (le_of_not_gt hi) (hg.1.1 i))⟩
    · exact ⟨i, Or.inr (le_antisymm (hg.1.2 i) (le_of_not_gt hi))⟩
  · rintro ⟨hg, i, hi | hi⟩
    · refine ⟨hg, fun hall => ?_⟩
      have h := (hall i).1
      rw [hi] at h
      exact lt_irrefl _ h
    · refine ⟨hg, fun hall => ?_⟩
      have h := (hall i).2
      rw [hi] at h
      exact lt_irrefl _ h

variable [Group G] [IsTopologicalGroup G]

/-- No original lattice translate of a strict domain's frontier enters its interior. -/
theorem strict_domain_translated_frontier_avoids_interior (Gamma : Subgroup G) (D : Set G)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (y : G) (hy : y ∈ frontier D) (gamma : Gamma) : y * gamma ∉ interior D := by
  by_cases hgamma : gamma = 1
  · simpa only [hgamma, Subgroup.coe_one, mul_one] using hy.2
  · have hd : Disjoint ((Homeomorph.mulRight (gamma : G)) '' D) (interior D) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨g, hg, rfl⟩ hx
      have he : gamma = 1 := (huniq g).unique (interior_subset hx) (by simpa using hg)
      exact hgamma he
    have hclosure := hd.closure_left isOpen_interior
    have hym : y * gamma ∈ closure ((Homeomorph.mulRight (gamma : G)) '' D) := by
      rw [← (Homeomorph.mulRight (gamma : G)).image_closure]
      exact ⟨y, hy.1, rfl⟩
    exact fun h => Set.disjoint_left.mp hclosure hym h

omit [TopologicalSpace G] [Group G] [IsTopologicalGroup G] in
/-- A coordinate point inside the closed cell near its open-cell complement
belongs to the explicit original coordinate-strip cover. -/
theorem coordinate_near_complement_mem_strip (a : Fin m → ℝ) (x y : Fin m → ℝ)
    (hx : x ∈ Set.Icc a (fun i => a i + 1))
    (hy : ¬ ∀ i, a i < y i ∧ y i < a i + 1) (t : ℝ) (hxy : dist x y ≤ t) :
    x ∈ coordinateBoundaryStrip a t := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hy
  have hd : |x i - y i| ≤ t := (dist_le_pi_dist x y i).trans hxy
  rcases not_and_or.mp hi with hi | hi
  · have hxi : x i ≤ a i + t := by
      have hya := le_of_not_gt hi
      have h := (abs_le.mp hd).2
      linarith
    apply Set.mem_iUnion.mpr
    refine ⟨i, Or.inl ⟨hx.1, ?_⟩⟩
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hxi
    · simpa [Function.update_of_ne hji] using hx.2 j
  · have hxi : a i + 1 - t ≤ x i := by
      have hya := le_of_not_gt hi
      have h := (abs_le.mp hd).1
      linarith
    apply Set.mem_iUnion.mpr
    refine ⟨i, Or.inr ⟨?_, hx.2⟩⟩
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hxi
    · simpa [Function.update_of_ne hji] using hx.1 j

end GMZP0
