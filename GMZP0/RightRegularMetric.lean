import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-! A concrete right-invariant metric from all translates of one fixed
distance peak. This first construction does not yet identify its topology. -/
noncomputable section
open Set Metric
open scoped BoundedContinuousFunction
namespace GMZP0
variable {G : Type*} [Group G] [MetricSpace G]

/-- A fixed peak at the original identity, supported in its unit ball. -/
def identityMetricPeak (x : G) : ℝ := max 0 (1 - dist x 1)

/-- The peak has values in the fixed unit interval. -/
theorem identity_metric_peak_bounds (x : G) :
    0 ≤ identityMetricPeak x ∧ identityMetricPeak x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [dist_nonneg (x := x) (y := 1)])⟩

/-- The peak is one exactly at the original identity. -/
theorem identity_metric_peak_eq_one (x : G) : identityMetricPeak x = 1 ↔ x = 1 := by
  unfold identityMetricPeak
  constructor
  · intro h
    have hd : 1 - dist x 1 = 1 := by
      rcases max_cases (0 : ℝ) (1 - dist x 1) with hmax | hmax
      · linarith [hmax.1]
      · exact hmax.1.symm.trans h
    exact dist_eq_zero.mp (by linarith)
  · rintro rfl
    simp

/-- The peak is 1-Lipschitz in the initial coordinate metric. -/
theorem identity_metric_peak_lipschitz : LipschitzWith 1 (identityMetricPeak : G → ℝ) := by
  have hf : LipschitzWith 1 (fun x : G => 1 - dist x 1) := by
    apply LipschitzWith.mk_one
    intro x y
    rw [Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]
    exact abs_dist_sub_le x y (1 : G)
  exact hf.const_max 0

variable [IsTopologicalGroup G]

/-- All original left translates of the fixed peak, viewed as bounded
continuous functions of the auxiliary group variable. -/
def rightRegularPeak (g : G) : G →ᵇ ℝ where
  toFun z := identityMetricPeak (g * z)
  continuous_toFun := identity_metric_peak_lipschitz.continuous.comp (continuous_const.mul continuous_id)
  map_bounded' := by
    refine ⟨1, fun x y => ?_⟩
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [(identity_metric_peak_bounds (g * x)).1,
      (identity_metric_peak_bounds (g * y)).2], by linarith [(identity_metric_peak_bounds (g * x)).2,
      (identity_metric_peak_bounds (g * y)).1]⟩

/-- The complete translate family distinguishes the original group elements. -/
theorem right_regular_peak_injective : Function.Injective (rightRegularPeak : G → G →ᵇ ℝ) := by
  intro g h he
  have hp := congrArg (fun f : G →ᵇ ℝ => f g⁻¹) he
  change identityMetricPeak (g * g⁻¹) = identityMetricPeak (h * g⁻¹) at hp
  have h1 : identityMetricPeak (h * g⁻¹) = 1 := by simpa [identityMetricPeak] using hp.symm
  have := (identity_metric_peak_eq_one _).mp h1
  exact (mul_inv_eq_one.mp this).symm

/-- The constructed distance is bounded by one everywhere. The later
coordinate comparisons therefore have local, rather than global, scope. -/
theorem right_regular_peak_dist_le_one (g h : G) :
    dist (rightRegularPeak g) (rightRegularPeak h) ≤ 1 := by
  apply (BoundedContinuousFunction.dist_le (by norm_num)).mpr
  intro z
  change dist (identityMetricPeak (g * z)) (identityMetricPeak (h * z)) ≤ 1
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [(identity_metric_peak_bounds (g * z)).1,
    (identity_metric_peak_bounds (h * z)).2], by linarith [(identity_metric_peak_bounds (g * z)).2,
    (identity_metric_peak_bounds (h * z)).1]⟩

/-- Simultaneous right translation only permutes the full auxiliary group. -/
theorem right_regular_peak_dist_right (g h a : G) :
    dist (rightRegularPeak (g * a)) (rightRegularPeak (h * a)) =
      dist (rightRegularPeak g) (rightRegularPeak h) := by
  have hle (u v b : G) : dist (rightRegularPeak (u * b)) (rightRegularPeak (v * b)) ≤
      dist (rightRegularPeak u) (rightRegularPeak v) := by
    apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro z
    change dist (identityMetricPeak ((u * b) * z)) (identityMetricPeak ((v * b) * z)) ≤ _
    rw [mul_assoc, mul_assoc]
    exact BoundedContinuousFunction.dist_coe_le_dist (f := rightRegularPeak u) (g := rightRegularPeak v) (b * z)
  exact le_antisymm (hle g h a) (by simpa [mul_assoc] using hle (g * a) (h * a) a⁻¹)

/-- Evaluation at the inverse of the second point detects its exact
relative displacement, up to the fixed truncation at one. -/
theorem right_regular_peak_relative_lower (g h : G) :
    min 1 (dist (g * h⁻¹) 1) ≤ dist (rightRegularPeak g) (rightRegularPeak h) := by
  have he := BoundedContinuousFunction.dist_coe_le_dist
    (f := rightRegularPeak g) (g := rightRegularPeak h) h⁻¹
  change dist (identityMetricPeak (g * h⁻¹)) (identityMetricPeak (h * h⁻¹)) ≤ _ at he
  simp only [mul_inv_cancel, identityMetricPeak, dist_self, sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
    Real.dist_eq] at he
  have hd := dist_nonneg (x := g * h⁻¹) (y := (1 : G))
  by_cases ht : dist (g * h⁻¹) 1 ≤ 1
  · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)] at he
    rw [min_eq_right ht]
    linarith
  · rw [max_eq_left (by linarith)] at he
    rw [min_eq_left (by linarith)]
    simpa using he

/-- A genuine metric, obtained by the injective original translate map. -/
@[instance_reducible] def rightRegularRawMetric : MetricSpace G :=
  MetricSpace.induced rightRegularPeak right_regular_peak_injective inferInstance

/-- Every actual right group translation is isometric for the new metric. -/
theorem right_regular_raw_metric_isometry (a : G) :
    @Isometry G G (rightRegularRawMetric (G := G)).toPseudoEMetricSpace
      (rightRegularRawMetric (G := G)).toPseudoEMetricSpace (fun x => x * a) := by
  apply (@isometry_iff_dist_eq G G (rightRegularRawMetric (G := G)).toPseudoMetricSpace
    (rightRegularRawMetric (G := G)).toPseudoMetricSpace _).mpr
  exact fun g h => right_regular_peak_dist_right g h a

end GMZP0
