import GMZP0.CompactCoordinateLipschitz

/-! Uniform actual representatives of nearby cosets. A compact original
cover and the literal coset-distance formula construct the lifts; no
nearest lattice point or independently rounded representative is used. -/
noncomputable section
open Set Metric
namespace GMZP0
variable {H : Type*} [Group H] [PseudoMetricSpace H]
  (Lambda : Subgroup H) [MetricSpace (H ⧸ Lambda)]

local instance compactLiftQuotientTopology : TopologicalSpace (H ⧸ Lambda) :=
  (inferInstance : MetricSpace (H ⧸ Lambda)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- A compact actual covering set gives compactness for the supplied
quotient metric satisfying the literal original coset-distance formula. -/
theorem coset_metric_compact_of_cover (C : Set H) (hC : IsCompact C)
    (hcover : ∀ h : H, ∃ gamma : Lambda, h * gamma ∈ C)
    (hdist : ∀ g h : H, dist (QuotientGroup.mk g : H ⧸ Lambda) (QuotientGroup.mk h) =
      originalCosetInfDist Lambda g h) : CompactSpace (H ⧸ Lambda) := by
  have hsur : (QuotientGroup.mk : H → H ⧸ Lambda) '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨gamma, hg⟩ := hcover g
    exact ⟨g * gamma, hg, QuotientGroup.mk_mul_of_mem g gamma.property⟩
  apply isCompact_univ_iff.mp
  rw [← hsur]
  exact hC.image (quotient_mk_lipschitz_of_coset_formula Lambda hdist).continuous

/-- The supplied metric has the genuine quotient topology: the original
compact cover makes the quotient map a quotient map for that metric. -/
theorem coset_metric_isQuotientMap (C : Set H) (hC : IsCompact C)
    (hcover : ∀ h : H, ∃ gamma : Lambda, h * gamma ∈ C)
    (hdist : ∀ g h : H, dist (QuotientGroup.mk g : H ⧸ Lambda) (QuotientGroup.mk h) =
      originalCosetInfDist Lambda g h) :
    Topology.IsQuotientMap (QuotientGroup.mk : H → H ⧸ Lambda) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hq := (quotient_mk_lipschitz_of_coset_formula Lambda hdist).continuous
  have hc : Continuous (fun z : C => (QuotientGroup.mk z.val : H ⧸ Lambda)) :=
    hq.comp continuous_subtype_val
  have hsur : Function.Surjective (fun z : C => (QuotientGroup.mk z.val : H ⧸ Lambda)) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨gamma, hg⟩ := hcover g
    exact ⟨⟨g * gamma, hg⟩, QuotientGroup.mk_mul_of_mem g gamma.property⟩
  exact Topology.IsQuotientMap.of_comp continuous_subtype_val hq
    (Topology.IsQuotientMap.of_surjective_continuous hsur hc)

/-- Exact topology identification, without assuming compatibility of the
quotient metric as an additional independent condition. -/
theorem coset_metric_topology_eq_coinduced (C : Set H) (hC : IsCompact C)
    (hcover : ∀ h : H, ∃ gamma : Lambda, h * gamma ∈ C)
    (hdist : ∀ g h : H, dist (QuotientGroup.mk g : H ⧸ Lambda) (QuotientGroup.mk h) =
      originalCosetInfDist Lambda g h) :
    (inferInstance : TopologicalSpace (H ⧸ Lambda)) =
      TopologicalSpace.coinduced (QuotientGroup.mk : H → H ⧸ Lambda) inferInstance :=
  (coset_metric_isQuotientMap Lambda C hC hcover hdist).eq_coinduced

variable [LocallyCompactSpace H]

/-- One compact enlargement and positive radius precede every nearby
quotient pair. The first representative stays in the original cover;
the second is an actual original lattice translate at distance at most 2d. -/
theorem compact_coset_pair_lifts (C : Set H) (hC : IsCompact C)
    (hcover : ∀ h : H, ∃ gamma : Lambda, h * gamma ∈ C)
    (hdist : ∀ g h : H, dist (QuotientGroup.mk g : H ⧸ Lambda) (QuotientGroup.mk h) =
      originalCosetInfDist Lambda g h) :
    ∃ E : Set H, IsCompact E ∧ C ⊆ E ∧ ∃ r : ℝ, 0 < r ∧
      ∀ x y : H ⧸ Lambda, dist x y < r → ∃ u v : H,
        u ∈ C ∧ v ∈ E ∧ QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧
          dist u v ≤ 2 * dist x y := by
  obtain ⟨s, hs, hE⟩ := hC.exists_isCompact_cthickening
  refine ⟨cthickening s C, hE, self_subset_cthickening C, s / 2, by positivity, ?_⟩
  intro x y hxy
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
  obtain ⟨gamma, hu⟩ := hcover g
  let u := g * gamma
  have hux : (QuotientGroup.mk u : H ⧸ Lambda) = x :=
    (QuotientGroup.mk_mul_of_mem g gamma.property).trans hg
  by_cases heq : x = y
  · refine ⟨u, u, hu, self_subset_cthickening C hu, hux, hux.trans heq, ?_⟩
    simp only [dist_self]
    positivity
  · obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective y
    have hd : 0 < dist x y := dist_pos.mpr heq
    have hclose : originalCosetInfDist Lambda u v < 2 * dist x y := by
      rw [← hdist, hux, hv]
      linarith
    obtain ⟨delta, hdelta⟩ := (original_coset_infDist_lt_iff Lambda u v _).mp hclose
    refine ⟨u, v * delta, hu, ?_, hux,
      (QuotientGroup.mk_mul_of_mem v delta.property).trans hv, hdelta.le⟩
    apply mem_cthickening_of_dist_le (v * delta) u s C hu
    rw [dist_comm]
    have hsmall : 2 * dist x y < s := by linarith
    exact (hdelta.trans hsmall).le

/-- Local Lipschitz control of the actual coordinate functions gives
uniform difference bounds on the constructed original pair lifts.
All constants and the compact enlargement precede every quotient pair. -/
theorem compact_coset_coordinate_pair_lifts {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (C : Set H) (hC : IsCompact C)
    (hcover : ∀ h : H, ∃ gamma : Lambda, h * gamma ∈ C)
    (hdist : ∀ g h : H, dist (QuotientGroup.mk g : H ⧸ Lambda) (QuotientGroup.mk h) =
      originalCosetInfDist Lambda g h)
    (f : H → X) (hf : LocallyLipschitz f) (g : H → Y) (hg : LocallyLipschitz g) :
    ∃ E : Set H, IsCompact E ∧ ∃ M B r : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ 0 < r ∧
      ∀ x y : H ⧸ Lambda, dist x y < r → ∃ u v : H,
        u ∈ E ∧ v ∈ E ∧ QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧
          dist (f u) (f v) ≤ M * dist x y ∧ dist (g u) (g v) ≤ B * dist x y := by
  obtain ⟨E, hE, hCE, r, hr, hlift⟩ := compact_coset_pair_lifts Lambda C hC hcover hdist
  obtain ⟨M, hM⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hE hf.locallyLipschitzOn
  obtain ⟨B, hB⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hE hg.locallyLipschitzOn
  refine ⟨E, hE, 2 * M, 2 * B, r, by positivity, by positivity, hr, ?_⟩
  intro x y hxy
  obtain ⟨u, v, hu, hv, hux, hvy, huv⟩ := hlift x y hxy
  refine ⟨u, v, hCE hu, hv, hux, hvy, ?_, ?_⟩
  · exact (hM.dist_le_mul u (hCE hu) v hv).trans
      ((mul_le_mul_of_nonneg_left huv M.coe_nonneg).trans_eq (by ring))
  · exact (hB.dist_le_mul u (hCE hu) v hv).trans
      ((mul_le_mul_of_nonneg_left huv B.coe_nonneg).trans_eq (by ring))

end GMZP0
