import GMZP0.BoundaryOrbitEstimate
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual boundary visit fractions and an exact obstruction to replacing
quantitative equidistribution by a Haar-null boundary alone. -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal
namespace GMZP0
variable {X Y I : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Fintype I]

/-- Every visit to the original t-tube is counted and bounded by the
explicit majorant. There is no deletion or modification of the orbit. -/
theorem orbit_boundary_visit_fraction_le (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure nu]
    (pi : X → Y) (hp : MeasurePreserving pi mu nu) (J : ℝ≥0) (hJ : LipschitzWith J pi)
    (S : Set Y) {t : ℝ} (ht : 0 < t) (u : I → X) (alpha : ℝ)
    (heq : LipschitzOrbitDiscrepancy mu u alpha) :
    realUniformMean (fun i => (boundaryTube S t).indicator (fun _ => (1 : ℝ)) (pi (u i))) ≤
      (nu (boundaryTube S (2 * t))).toReal + alpha * (1 + t⁻¹ * J) := by
  apply le_trans (realUniformMean_mono _ _ ?_)
    (orbit_boundary_majorant_mean_le mu nu pi hp J hJ S ht u alpha heq)
  intro i
  by_cases h : pi (u i) ∈ boundaryTube S t
  · rw [Set.indicator_of_mem h]
    exact (boundary_cutoff_zero_near S ht _ h.1 h.2.le).1.ge
  · rw [Set.indicator_of_notMem h]
    exact (boundary_cutoff_bounds S t _).1

omit [PseudoMetricSpace X] [MeasurableSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] in
/-- A Haar-null boundary may contain every point of every finite constant
orbit, even under a normalized Lebesgue probability on a compact cell.
Thus small measure alone cannot give the required orbit estimate. -/
theorem null_boundary_full_orbit_visits [Nonempty I] :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
    (volume.restrict (Set.Icc (0 : ℝ) 1)) ({0} : Set ℝ) = 0 ∧
    ∀ t : ℝ, 0 < t → realUniformMean (fun _ : I => boundaryMajorant ({0} : Set ℝ) t 0) = 1 := by
  refine ⟨⟨by simp [Real.volume_Icc]⟩, ?_, ?_⟩
  · rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left (measure_singleton (0 : ℝ))
  · intro t ht
    rw [realUniformMean_const]
    exact (boundary_cutoff_zero_near ({0} : Set ℝ) ht 0 (Set.singleton_nonempty 0)
      (by simpa using ht.le)).1

end GMZP0
