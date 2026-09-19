import GMZP0.RightRegularMetric
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.Group.Pointwise

/-! Compact support converts local Lipschitz multiplication into two-sided
local metric control for the concrete right-regular distance. -/
noncomputable section
open Set Metric
open scoped BoundedContinuousFunction NNReal Topology
namespace GMZP0
variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G] [ProperSpace G]

/-- On each original compact set, the new distance is bounded by a
constant times the original distance, uniformly over all auxiliary translates. -/
theorem right_regular_peak_compact_upper
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2))
    (K : Set G) (hK : IsCompact K) :
    ∃ L : ℝ≥0, LipschitzOnWith L (rightRegularPeak : G → G →ᵇ ℝ) K := by
  let B := closedBall (1 : G) 1
  let Z := (fun p : G × G => p.1⁻¹ * p.2) '' (K ×ˢ B)
  have hZ : IsCompact Z := (hK.prod (isCompact_closedBall _ _)).image
    (continuous_fst.inv.mul continuous_snd)
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hK.prod hZ) hmul.locallyLipschitzOn
  refine ⟨L, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  apply (BoundedContinuousFunction.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro z
  change dist (identityMetricPeak (x * z)) (identityMetricPeak (y * z)) ≤ _
  by_cases hzero : identityMetricPeak (x * z) = 0 ∧ identityMetricPeak (y * z) = 0
  · rw [hzero.1, hzero.2, dist_self]
    positivity
  · have hz : z ∈ Z := by
      have hmem (g : G) (hg : g ∈ K) (hp : identityMetricPeak (g * z) ≠ 0) : z ∈ Z := by
        have hd : dist (g * z) 1 ≤ 1 := by
          by_contra hn
          apply hp
          exact max_eq_left (by linarith)
        exact ⟨(g, g * z), ⟨hg, hd⟩, by simp⟩
      by_cases hx0 : identityMetricPeak (x * z) = 0
      · exact hmem y hy (fun hy0 => hzero ⟨hx0, hy0⟩)
      · exact hmem x hx hx0
    have hb := hL.dist_le_mul (x, z) ⟨hx, hz⟩ (y, z) ⟨hy, hz⟩
    exact (identity_metric_peak_lipschitz.dist_le_mul (x * z) (y * z)).trans
      (by simpa only [one_mul, NNReal.coe_one, dist_prod_same_right] using hb)

omit [ProperSpace G] in
/-- Small new distance controls the actual relative displacement without
any nearest point, lattice or quotient argument. -/
theorem right_regular_peak_relative_small (g h : G)
    (hsmall : dist (rightRegularPeak g) (rightRegularPeak h) < 1) :
    dist (g * h⁻¹) 1 ≤ dist (rightRegularPeak g) (rightRegularPeak h) := by
  rcases min_le_iff.mp (right_regular_peak_relative_lower g h) with hbad | hgood
  · linarith
  · exact hgood

/-- The original distance on each compact set is bounded by a uniform
multiple of the constructed distance. Large distances use the compact diameter. -/
theorem right_regular_peak_compact_lower
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2))
    (K : Set G) (hK : IsCompact K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ g ∈ K, ∀ h ∈ K,
      dist g h ≤ L * dist (rightRegularPeak g) (rightRegularPeak h) := by
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_closedBall (1 : G) 1).prod hK) hmul.locallyLipschitzOn
  refine ⟨C + diam K, add_nonneg C.coe_nonneg diam_nonneg, ?_⟩
  intro g hg h hh
  by_cases hs : dist (rightRegularPeak g) (rightRegularPeak h) < 1
  · have hrel := right_regular_peak_relative_small g h hs
    have hb := hC.dist_le_mul (g * h⁻¹, h) ⟨hrel.trans hs.le, hh⟩ (1, h)
      ⟨by simp, hh⟩
    have hd : dist g h ≤ C * dist (g * h⁻¹) 1 := by simpa [mul_assoc] using hb
    calc
      dist g h ≤ C * dist (rightRegularPeak g) (rightRegularPeak h) :=
        hd.trans (mul_le_mul_of_nonneg_left hrel C.coe_nonneg)
      _ ≤ (C + diam K) * dist (rightRegularPeak g) (rightRegularPeak h) := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right diam_nonneg) dist_nonneg
  · have hd := dist_le_diam_of_mem hK.isBounded hg hh
    have hn := dist_nonneg (x := rightRegularPeak g) (y := rightRegularPeak h)
    have hdiam := diam_nonneg (s := K)
    have hc := C.coe_nonneg
    have hs' : 1 ≤ dist (rightRegularPeak g) (rightRegularPeak h) := le_of_not_gt hs
    nlinarith

/-- The original-to-new identity is locally Lipschitz, proved from the
original locally Lipschitz group multiplication and compact unit balls. -/
theorem right_regular_peak_locally_lipschitz
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) :
    LocallyLipschitz (rightRegularPeak : G → G →ᵇ ℝ) := by
  intro g
  obtain ⟨L, hL⟩ := right_regular_peak_compact_upper hmul
    (closedBall g 1) (isCompact_closedBall _ _)
  exact ⟨L, closedBall g 1, closedBall_mem_nhds _ (by norm_num), hL⟩

/-- One constant controls the inverse identity on the entire new unit
ball about each original point. The containing compact set is constructed. -/
theorem right_regular_peak_local_inverse
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) (h : G) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : G,
      dist (rightRegularPeak x) (rightRegularPeak h) < 1 →
      dist (rightRegularPeak y) (rightRegularPeak h) < 1 →
      dist x y ≤ L * dist (rightRegularPeak x) (rightRegularPeak y) := by
  let K := (fun z : G => z * h) '' closedBall (1 : G) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).image (continuous_id.mul continuous_const)
  obtain ⟨L, hL, hbound⟩ := right_regular_peak_compact_lower hmul K hK
  refine ⟨L, hL, fun x y hx hy => ?_⟩
  have hmem (g : G) (hg : dist (rightRegularPeak g) (rightRegularPeak h) < 1) : g ∈ K :=
    ⟨g * h⁻¹, (right_regular_peak_relative_small g h hg).trans hg.le, by simp [mul_assoc]⟩
  exact hbound x (hmem x hx) y (hmem y hy)

end GMZP0
