import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Explicit distance cutoffs for the actual boundary set. The empty boundary
is treated separately: `infDist` alone is zero on the empty set. No small-tube
measure estimate is assumed to follow merely from continuity or compactness. -/
noncomputable section
open Set Metric MeasureTheory
namespace GMZP0
variable {X : Type*} [PseudoMetricSpace X]

/-- The open metric tube, with its correct empty-set convention. -/
def boundaryTube (S : Set X) (r : ℝ) : Set X :=
  {x | S.Nonempty ∧ infDist x S < r}

/-- One on the t-tube, zero outside the 2t-tube, and linear in between. -/
def boundaryMajorant (S : Set X) (t : ℝ) (x : X) : ℝ := by
  classical
  exact if S.Nonempty then min 1 (max 0 (2 - infDist x S / t)) else 0

/-- The base cutoff multiplying the unchanged original observation. -/
def boundaryCutoff (S : Set X) (t : ℝ) (x : X) : ℝ :=
  1 - boundaryMajorant S t x

/-- Empty boundaries require no truncation. -/
theorem boundary_cutoff_empty (t : ℝ) (x : X) :
    boundaryMajorant ∅ t x = 0 ∧ boundaryCutoff ∅ t x = 1 := by
  simp [boundaryMajorant, boundaryCutoff]

/-- Both the majorant and cutoff take values in the closed unit interval. -/
theorem boundary_cutoff_bounds (S : Set X) (t : ℝ) (x : X) :
    0 ≤ boundaryMajorant S t x ∧ boundaryMajorant S t x ≤ 1 ∧
      0 ≤ boundaryCutoff S t x ∧ boundaryCutoff S t x ≤ 1 := by
  have h : 0 ≤ boundaryMajorant S t x ∧ boundaryMajorant S t x ≤ 1 := by
    unfold boundaryMajorant
    split_ifs
    · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · norm_num
  dsimp [boundaryCutoff]
  exact ⟨h.1, h.2, sub_nonneg.mpr h.2, sub_le_self _ h.1⟩

/-- The actual closed t-neighborhood is fully suppressed. -/
theorem boundary_cutoff_zero_near (S : Set X) {t : ℝ} (ht : 0 < t)
    (x : X) (hS : S.Nonempty) (hx : infDist x S ≤ t) :
    boundaryMajorant S t x = 1 ∧ boundaryCutoff S t x = 0 := by
  have hd : infDist x S / t ≤ 1 := (div_le_one ht).mpr hx
  have hb : boundaryMajorant S t x = 1 := by
    simp only [boundaryMajorant, if_pos hS]
    exact min_eq_left (le_trans (show 1 ≤ 2 - infDist x S / t by linarith) (le_max_right _ _))
  simp [boundaryCutoff, hb]

/-- The majorant vanishes outside the open 2t-neighborhood, including its outer edge. -/
theorem boundary_majorant_zero_outside (S : Set X) {t : ℝ} (ht : 0 < t)
    (x : X) (hx : x ∉ boundaryTube S (2 * t)) : boundaryMajorant S t x = 0 := by
  by_cases hS : S.Nonempty
  · have hd : 2 * t ≤ infDist x S := by
      exact le_of_not_gt (fun h => hx ⟨hS, h⟩)
    have hdiv : 2 ≤ infDist x S / t := (le_div_iff₀ ht).mpr hd
    simp [boundaryMajorant, hS, max_eq_left (show 2 - infDist x S / t ≤ 0 by linarith)]
  · simp [boundaryMajorant, hS]

/-- The cutoff equals one away from the doubled tube. -/
theorem boundary_cutoff_one_outside (S : Set X) {t : ℝ} (ht : 0 < t)
    (x : X) (hx : x ∉ boundaryTube S (2 * t)) : boundaryCutoff S t x = 1 := by
  simp [boundaryCutoff, boundary_majorant_zero_outside S ht x hx]

/-- The explicitly constructed majorant has Lipschitz constant at most 1/t. -/
theorem boundary_majorant_lipschitz (S : Set X) {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal t⁻¹) (boundaryMajorant S t) := by
  by_cases hS : S.Nonempty
  · have ha : LipschitzWith (Real.toNNReal t⁻¹) (fun x => 2 - infDist x S / t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)]
      calc
        dist (2 - infDist x S / t) (2 - infDist y S / t) =
            dist (infDist y S) (infDist x S) / t := by
          simp only [Real.dist_eq]
          rw [show (2 - infDist x S / t) - (2 - infDist y S / t) =
            (infDist y S - infDist x S) / t by ring, abs_div, abs_of_pos ht]
        _ ≤ dist y x / t := div_le_div_of_nonneg_right
          (by simpa using (lipschitz_infDist_pt S).dist_le_mul y x) ht.le
        _ = t⁻¹ * dist x y := by rw [dist_comm]; ring
    have he : boundaryMajorant S t = fun x => min 1 (max 0 (2 - infDist x S / t)) := by
      funext x
      simp only [boundaryMajorant, if_pos hS]
    rw [he]
    exact (ha.const_max 0).const_min 1
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [boundaryMajorant, if_neg hS, dist_self]
    positivity

/-- Complementing the majorant preserves exactly the same Lipschitz bound. -/
theorem boundary_cutoff_lipschitz (S : Set X) {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal t⁻¹) (boundaryCutoff S t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (boundary_majorant_lipschitz S ht).dist_le_mul x y
  simpa only [boundaryCutoff, Real.dist_eq,
    show (1 - boundaryMajorant S t x) - (1 - boundaryMajorant S t y) =
      -(boundaryMajorant S t x - boundaryMajorant S t y) by ring, abs_neg] using h

variable [MeasurableSpace X] [BorelSpace X]

/-- The majorant is genuinely integrable for every finite original measure. -/
theorem boundary_majorant_integrable (mu : Measure X) [IsFiniteMeasure mu]
    (S : Set X) {t : ℝ} (ht : 0 < t) : Integrable (boundaryMajorant S t) mu := by
  apply (integrable_const (1 : ℝ)).mono'
    (boundary_majorant_lipschitz S ht).continuous.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (boundary_cutoff_bounds S t x).1]
    exact (boundary_cutoff_bounds S t x).2.1)

omit [BorelSpace X] in
/-- Its integral is bounded by the actual doubled-tube measure, not by an assumed orbit frequency. -/
theorem boundary_majorant_integral_le_tube (mu : Measure X) [IsFiniteMeasure mu]
    (S : Set X) {t : ℝ} (ht : 0 < t) :
    (∫ x, boundaryMajorant S t x ∂mu) ≤ (mu (boundaryTube S (2 * t))).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  apply integral_le_measure
  · intro x _
    exact (boundary_cutoff_bounds S t x).2.1
  · intro x hx
    exact (boundary_majorant_zero_outside S ht x hx).le

end GMZP0
