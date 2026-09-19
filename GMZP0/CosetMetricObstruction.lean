import GMZP0.OriginalCosetMetric
import Mathlib.Tactic.NormNum

/-! An exact source-metric obstruction: pulling back Euclidean distance
by the cubic coordinate gives a metric in which integer translation is
not isometric. The right-isometry input must therefore be justified. -/
noncomputable section
namespace GMZP0

/-- Euclidean distance pulled back through an injective cubic coordinate. -/
@[instance_reducible] def cubicCoordinateMetric : MetricSpace ℝ :=
  MetricSpace.induced (fun x : ℝ => x ^ 3)
    ((show Odd (3 : ℕ) by decide).strictMono_pow (R := ℝ)).injective inferInstance

/-- The actual integer translation changes the distance from 1 to 7.
This is an obstruction to choosing arbitrary coordinate metrics, not P0. -/
theorem cubic_coordinate_translation_not_isometry :
    ¬ @Isometry ℝ ℝ cubicCoordinateMetric.toPseudoEMetricSpace
      cubicCoordinateMetric.toPseudoEMetricSpace (fun x : ℝ => x + 1) := by
  intro h
  have hd := (@isometry_iff_dist_eq ℝ ℝ cubicCoordinateMetric.toPseudoMetricSpace
    cubicCoordinateMetric.toPseudoMetricSpace (fun x : ℝ => x + 1)).mp h 0 1
  change |((0 : ℝ) + 1) ^ 3 - (1 + 1) ^ 3| = |(0 : ℝ) ^ 3 - 1 ^ 3| at hd
  norm_num at hd

end GMZP0
