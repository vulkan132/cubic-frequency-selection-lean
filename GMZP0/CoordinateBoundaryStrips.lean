import GMZP0.MetricBoundaryCutoff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact linear-in-width bounds for the original unit coordinate cell.
The final theorem is a coordinate-space tube estimate. Passing from the
actual quotient metric to this cover still requires quantitative charts. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace GMZP0
variable {m : ℕ}

def coordinateLowerStrip (a : Fin m → ℝ) (t : ℝ) (i : Fin m) : Set (Fin m → ℝ) :=
  Set.Icc a (Function.update (fun j => a j + 1) i (a i + t))

def coordinateUpperStrip (a : Fin m → ℝ) (t : ℝ) (i : Fin m) : Set (Fin m → ℝ) :=
  Set.Icc (Function.update a i (a i + 1 - t)) (fun j => a j + 1)

def coordinateBoundaryStrip (a : Fin m → ℝ) (t : ℝ) : Set (Fin m → ℝ) :=
  ⋃ i : Fin m, coordinateLowerStrip a t i ∪ coordinateUpperStrip a t i

/-- Both actual faces of every coordinate of the closed unit box. -/
def coordinateCellFaces (a : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {u | u ∈ Set.Icc a (fun i => a i + 1) ∧ ∃ i, u i = a i ∨ u i = a i + 1}

/-- A lower coordinate strip has exactly its width as volume. -/
theorem coordinate_lower_strip_volume (a : Fin m → ℝ) (t : ℝ) (i : Fin m) :
    volume (coordinateLowerStrip a t i) = ENNReal.ofReal t := by
  rw [coordinateLowerStrip, Real.volume_Icc_pi, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

/-- The opposite face has exactly the same strip volume. -/
theorem coordinate_upper_strip_volume (a : Fin m → ℝ) (t : ℝ) (i : Fin m) :
    volume (coordinateUpperStrip a t i) = ENNReal.ofReal t := by
  rw [coordinateUpperStrip, Real.volume_Icc_pi, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

/-- The original finite strip cover is Borel. -/
theorem coordinate_boundary_strip_measurable (a : Fin m → ℝ) (t : ℝ) :
    MeasurableSet (coordinateBoundaryStrip a t) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Icc.union measurableSet_Icc)

/-- The union of all 2m coordinate strips has volume at most 2mt. -/
theorem coordinate_boundary_strip_volume (a : Fin m → ℝ) (t : ℝ) :
    volume (coordinateBoundaryStrip a t) ≤ ENNReal.ofReal (2 * (m : ℝ) * t) := by
  calc
    volume (coordinateBoundaryStrip a t) ≤
        ∑' i : Fin m, volume (coordinateLowerStrip a t i ∪ coordinateUpperStrip a t i) :=
      measure_iUnion_le _
    _ ≤ ∑ i : Fin m, (ENNReal.ofReal t + ENNReal.ofReal t) := by
      rw [tsum_fintype]
      apply Finset.sum_le_sum
      intro i _
      simpa only [coordinate_lower_strip_volume, coordinate_upper_strip_volume] using
        measure_union_le (μ := volume) (coordinateLowerStrip a t i) (coordinateUpperStrip a t i)
    _ = ENNReal.ofReal (2 * (m : ℝ) * t) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

/-- A point in the original closed unit cell within distance t of an actual
coordinate face belongs to the explicit strip cover. -/
theorem coordinate_face_tube_subset_strip (a : Fin m → ℝ) (t : ℝ) :
    Set.Icc a (fun i => a i + 1) ∩ boundaryTube (coordinateCellFaces a) t ⊆
      coordinateBoundaryStrip a t := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hx.2.1).mp hx.2.2
  obtain ⟨i, hi | hi⟩ := hy.2
  · have hd : |x i - y i| < t := (dist_le_pi_dist x y i).trans_lt hxy
    have hxi : x i ≤ a i + t := by rw [hi] at hd; have := (abs_lt.mp hd).2; linarith
    apply Set.mem_iUnion.mpr
    refine ⟨i, Or.inl ⟨hx.1.1, ?_⟩⟩
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hxi
    · simpa [Function.update_of_ne hji] using hx.1.2 j
  · have hd : |x i - y i| < t := (dist_le_pi_dist x y i).trans_lt hxy
    have hxi : a i + 1 - t ≤ x i := by rw [hi] at hd; have := (abs_lt.mp hd).1; linarith
    apply Set.mem_iUnion.mpr
    refine ⟨i, Or.inr ⟨?_, hx.1.2⟩⟩
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hxi
    · simpa [Function.update_of_ne hji] using hx.1.1 j

/-- The actual coordinate face tube, restricted to its original unit cell,
has the explicit linear bound. This does not identify a quotient metric. -/
theorem coordinate_face_tube_volume (a : Fin m → ℝ) (t : ℝ) :
    volume (Set.Icc a (fun i => a i + 1) ∩ boundaryTube (coordinateCellFaces a) t) ≤
      ENNReal.ofReal (2 * (m : ℝ) * t) :=
  (measure_mono (coordinate_face_tube_subset_strip a t)).trans (coordinate_boundary_strip_volume a t)

end GMZP0
