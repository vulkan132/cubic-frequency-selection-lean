import GMZP0.RightRegularMetricBounds

/-! The constructed right-invariant metric has exactly the original
topology and is locally bi-Lipschitz with the initial coordinate metric. -/
noncomputable section
open Set Metric
open scoped BoundedContinuousFunction NNReal Topology
namespace GMZP0
variable {G : Type*} [Group G] [m : MetricSpace G] [IsTopologicalGroup G] [ProperSpace G]

/-- The identity from the original metric to the constructed metric is
locally Lipschitz; both metric structures are explicit. -/
theorem right_regular_original_to_raw_locally_lipschitz
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) :
    @LocallyLipschitz G G m.toPseudoEMetricSpace
      (rightRegularRawMetric (G := G)).toPseudoEMetricSpace id := by
  intro h
  obtain ⟨L, U, hU, hL⟩ := right_regular_peak_locally_lipschitz hmul h
  refine ⟨L, U, hU, ?_⟩
  apply @LipschitzOnWith.of_dist_le_mul G G m.toPseudoMetricSpace
    (rightRegularRawMetric (G := G)).toPseudoMetricSpace
  exact fun x hx y hy => hL.dist_le_mul x hx y hy

/-- The inverse identity is locally Lipschitz on a whole ball of the
constructed metric; no pre-existing topology agreement is assumed. -/
theorem right_regular_raw_to_original_locally_lipschitz
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) :
    @LocallyLipschitz G G (rightRegularRawMetric (G := G)).toPseudoEMetricSpace
      m.toPseudoEMetricSpace id := by
  intro h
  obtain ⟨L, hL, hbound⟩ := right_regular_peak_local_inverse hmul h
  refine ⟨Real.toNNReal L, {x | dist (rightRegularPeak x) (rightRegularPeak h) < 1}, ?_, ?_⟩
  · exact @Metric.ball_mem_nhds G (rightRegularRawMetric (G := G)).toPseudoMetricSpace h 1 (by norm_num)
  · apply @LipschitzOnWith.of_dist_le_mul G G
      (rightRegularRawMetric (G := G)).toPseudoMetricSpace m.toPseudoMetricSpace
    intro x hx y hy
    change dist x y ≤ (Real.toNNReal L : ℝ) * dist (rightRegularPeak x) (rightRegularPeak y)
    rw [Real.coe_toNNReal _ hL]
    exact hbound x y hx hy

/-- Two proved local Lipschitz identities identify the exact original
topology of the newly constructed right-invariant metric. -/
theorem right_regular_raw_topology
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) :
    (rightRegularRawMetric (G := G)).toUniformSpace.toTopologicalSpace =
      m.toUniformSpace.toTopologicalSpace := by
  have hnew := @LocallyLipschitz.continuous G G
    (rightRegularRawMetric (G := G)).toPseudoEMetricSpace m.toPseudoEMetricSpace id
    (right_regular_raw_to_original_locally_lipschitz hmul)
  have hold := @LocallyLipschitz.continuous G G m.toPseudoEMetricSpace
    (rightRegularRawMetric (G := G)).toPseudoEMetricSpace id
    (right_regular_original_to_raw_locally_lipschitz hmul)
  exact le_antisymm (continuous_id_iff_le.mp hnew) (continuous_id_iff_le.mp hold)

/-- A right-invariant metric retaining the original topology definitionally. -/
@[instance_reducible] def compatibleRightMetric
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) : MetricSpace G :=
  @MetricSpace.replaceTopology G m.toUniformSpace.toTopologicalSpace
    rightRegularRawMetric (right_regular_raw_topology hmul).symm

/-- The compatible right metric has the original topology. -/
theorem compatible_right_metric_topology
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) :
    (compatibleRightMetric hmul).toUniformSpace.toTopologicalSpace =
      m.toUniformSpace.toTopologicalSpace := rfl

/-- All original right translations, hence all original lattice translations,
are isometries of the constructed compatible metric. -/
theorem compatible_right_metric_isometry
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) (a : G) :
    @Isometry G G (compatibleRightMetric hmul).toPseudoEMetricSpace
      (compatibleRightMetric hmul).toPseudoEMetricSpace (fun x => x * a) := by
  have he : compatibleRightMetric hmul = (rightRegularRawMetric : MetricSpace G) :=
    MetricSpace.replaceTopology_eq _ _
  rw [he]
  exact right_regular_raw_metric_isometry a

/-- Local Lipschitz regularity holds in both directions, with the exact
same original elements and the explicitly constructed new metric. -/
theorem compatible_right_metric_local_comparison
    (hmul : LocallyLipschitz (fun p : G × G => p.1 * p.2)) :
    @LocallyLipschitz G G m.toPseudoEMetricSpace (compatibleRightMetric hmul).toPseudoEMetricSpace id ∧
      @LocallyLipschitz G G (compatibleRightMetric hmul).toPseudoEMetricSpace m.toPseudoEMetricSpace id := by
  have he : compatibleRightMetric hmul = (rightRegularRawMetric : MetricSpace G) :=
    MetricSpace.replaceTopology_eq _ _
  rw [he]
  exact ⟨right_regular_original_to_raw_locally_lipschitz hmul,
    right_regular_raw_to_original_locally_lipschitz hmul⟩

end GMZP0
