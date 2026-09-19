import GMZP0.CoordinateCellFrontier
import GMZP0.OriginalCoordinateBoundary

/-! Lift actual quotient boundary tubes through the literal coset-distance
formula, and cover them by original coordinate strips using local metric
control. The intended metrics and that control remain explicit inputs. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal
namespace GMZP0

/-- The open tube is Borel, including the empty-boundary case. -/
theorem metric_boundary_tube_measurable {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (S : Set X) (t : ℝ) :
    MeasurableSet (boundaryTube S t) := by
  by_cases hS : S.Nonempty
  · simpa only [boundaryTube, hS, true_and] using
      measurableSet_lt (continuous_infDist_pt S).measurable measurable_const
  · have he : boundaryTube S t = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ hx => hS hx.1)
    rw [he]
    exact MeasurableSet.empty

variable {G : Type*} [Group G] [PseudoMetricSpace G]

/-- Distance to the original right coset, with every original lattice point retained. -/
def originalCosetInfDist (Gamma : Subgroup G) (g h : G) : ℝ :=
  infDist g (Set.range (fun gamma : Gamma => h * gamma))

/-- A strict distance bound yields an actual original lattice translate,
without assuming a nearest representative exists. -/
theorem original_coset_infDist_lt_iff (Gamma : Subgroup G) (g h : G) (t : ℝ) :
    originalCosetInfDist Gamma g h < t ↔ ∃ gamma : Gamma, dist g (h * gamma) < t := by
  rw [originalCosetInfDist, infDist_lt_iff (Set.range_nonempty _)]
  constructor
  · rintro ⟨y, ⟨gamma, rfl⟩, hgamma⟩
    exact ⟨gamma, hgamma⟩
  · rintro ⟨gamma, hgamma⟩
    exact ⟨h * gamma, ⟨gamma, rfl⟩, hgamma⟩

variable (Gamma : Subgroup G) [PseudoMetricSpace (G ⧸ Gamma)]

local instance quotientBoundaryMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : PseudoMetricSpace (G ⧸ Gamma)).toUniformSpace.toTopologicalSpace

/-- The literal coset-distance formula already makes the actual quotient map 1-Lipschitz. -/
theorem quotient_mk_lipschitz_of_coset_formula
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h) :
    LipschitzWith 1 (QuotientGroup.mk : G → G ⧸ Gamma) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [hdist, NNReal.coe_one, one_mul]
  exact infDist_le_dist_of_mem ⟨(1 : Gamma), by simp⟩

variable [IsTopologicalGroup G] {m : ℕ}

/-- The image of the actual cell frontier under the original quotient map. -/
def originalCellFaceImage (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) : Set (G ⧸ Gamma) :=
  QuotientGroup.mk '' frontier (coordinateHalfOpenCell coord a)

omit [IsTopologicalGroup G] in
/-- The complete original face image is compact in the supplied quotient
metric satisfying the actual coset-distance formula. -/
theorem original_cell_face_image_compact (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ)
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h) : IsCompact (originalCellFaceImage Gamma coord a) := by
  have hK : IsCompact (frontier (coordinateHalfOpenCell coord a)) :=
    (coordinate_half_open_cell_compact_closure coord a).of_isClosed_subset isClosed_frontier
      frontier_subset_closure
  exact hK.image (quotient_mk_lipschitz_of_coset_formula Gamma hdist).continuous

/-- Actual quotient tubes lift to original lattice translates of faces;
strict-domain separation and local coordinate control then give the strip cover. -/
theorem original_quotient_face_tube_strip_cover (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ coordinateHalfOpenCell coord a)
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (L r : ℝ) (hL : 0 ≤ L)
    (hcoord : ∀ g ∈ coordinateHalfOpenCell coord a, ∀ v : G, dist g v < r →
      dist (coord g) (coord v) ≤ L * dist g v)
    (t : ℝ) (htr : t ≤ r) (g : G) (hg : g ∈ coordinateHalfOpenCell coord a)
    (hnear : (QuotientGroup.mk g : G ⧸ Gamma) ∈ boundaryTube (originalCellFaceImage Gamma coord a) t) :
    coord g ∈ coordinateBoundaryStrip a (L * t) := by
  obtain ⟨z, hz, hgz⟩ := (infDist_lt_iff hnear.1).mp hnear.2
  obtain ⟨y, hy, rfl⟩ := hz
  rw [hdist] at hgz
  obtain ⟨gamma, hgamma⟩ := (original_coset_infDist_lt_iff Gamma g y t).mp hgz
  have houtside := strict_domain_translated_frontier_avoids_interior Gamma _ huniq y hy gamma
  have hnot : ¬ ∀ i, a i < coord (y * gamma) i ∧ coord (y * gamma) i < a i + 1 := by
    intro hall
    apply houtside
    rw [coordinate_cell_interior]
    exact hall
  have hclose : dist (coord g) (coord (y * gamma)) ≤ L * t :=
    (hcoord g hg _ (hgamma.trans_le htr)).trans (mul_le_mul_of_nonneg_left hgamma.le hL)
  exact coordinate_near_complement_mem_strip a (coord g) (coord (y * gamma))
    ⟨fun i => (hg i).1, fun i => (hg i).2.le⟩ hnot (L * t) hclose

variable [MeasurableSpace G] [BorelSpace G] [BorelSpace (G ⧸ Gamma)]

/-- The actual quotient-metric face tube has a linear mass bound once the
literal distance formula and fixed local coordinate control are supplied. -/
theorem coordinate_quotient_face_tube_measure_le (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ coordinateHalfOpenCell coord a)
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (L r : ℝ) (hL : 0 ≤ L)
    (hcoord : ∀ g ∈ coordinateHalfOpenCell coord a, ∀ v : G, dist g v < r →
      dist (coord g) (coord v) ≤ L * dist g v)
    (t : ℝ) (htr : t ≤ r) :
    coordinateQuotientVolume Gamma coord a (boundaryTube (originalCellFaceImage Gamma coord a) t) ≤
      ENNReal.ofReal (2 * (m : ℝ) * (L * t)) := by
  apply coordinate_quotient_strip_event_bound Gamma coord a (L * t) _
    (metric_boundary_tube_measurable _ _)
  exact original_quotient_face_tube_strip_cover Gamma coord a huniq hdist L r hL hcoord t htr

end GMZP0
