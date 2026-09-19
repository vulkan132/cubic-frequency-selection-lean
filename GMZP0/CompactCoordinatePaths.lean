import GMZP0.CompactCoordinateLipschitz
import GMZP0.OriginalObservationCutoffGeometry
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Construct short original base paths by straight coordinate segments.
Local metric regularity of both directions is explicit and yields uniform
constants on a compact base chart before every nearby pair. -/
noncomputable section
open Set Metric Module
namespace GMZP0

/-- A locally bi-Lipschitz coordinate homeomorphism constructs uniformly
short paths from every compact-chart point to every sufficiently near point. -/
theorem compact_coordinate_short_paths {G : Type*} [PseudoMetricSpace G] {m : ℕ}
    (coord : G ≃ₜ (Fin m → ℝ)) (hcoord : LocallyLipschitz coord)
    (hinv : LocallyLipschitz coord.symm) (K : Set G) (hK : IsCompact K) :
    ∃ A r : ℝ, 0 ≤ A ∧ 0 < r ∧ ∀ g ∈ K, ∀ v : G, dist g v < r →
      ∃ p : Path g v, ∀ s, dist g (p s) ≤ A * dist g v := by
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  obtain ⟨L, r, hL, hr, hforward⟩ := compact_locally_lipschitz_uniform coord hcoord K hK
  obtain ⟨B, s, hB, hs, hback⟩ := compact_locally_lipschitz_uniform coord.symm hinv
    (coord '' K) (hK.image coord.continuous)
  have hden : 0 < L + 1 := by positivity
  refine ⟨B * L, min r (s / (L + 1)), mul_nonneg hB hL,
    lt_min hr (div_pos hs hden), ?_⟩
  intro g hg v hgv
  have hgv1 : dist g v < r := hgv.trans_le (min_le_left _ _)
  have hgv2 : dist g v < s / (L + 1) := hgv.trans_le (min_le_right _ _)
  have hcoorddist := hforward g hg v hgv1
  have hsmall : dist (coord g) (coord v) < s := by
    have h := (lt_div_iff₀ hden).mp hgv2
    nlinarith [dist_nonneg (x := g) (y := v)]
  let p : Path g v := {
    toFun := fun u => coord.symm ((Path.segment (coord g) (coord v)) u)
    continuous_toFun := coord.symm.continuous.comp (Path.segment (coord g) (coord v)).continuous
    source' := by simp
    target' := by simp }
  refine ⟨p, ?_⟩
  intro u
  have hseg : dist (coord g) ((Path.segment (coord g) (coord v)) u) ≤ dist (coord g) (coord v) := by
    rw [Path.segment_apply, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg u.property.1]
    simpa using mul_le_mul_of_nonneg_right u.property.2 (dist_nonneg (x := coord g) (y := coord v))
  have hb := hback (coord g) ⟨g, hg, rfl⟩ ((Path.segment (coord g) (coord v)) u)
    (hseg.trans_lt hsmall)
  change dist g (coord.symm ((Path.segment (coord g) (coord v)) u)) ≤ _
  rw [coord.symm_apply_apply] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hseg.trans hcoorddist) hB).trans_eq (by ring))

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (V : ObservationModule G) (Gamma : Subgroup G)
  {iota : Type*} [Fintype iota] {m : ℕ}
  [PseudoMetricSpace (G ⧸ Gamma)]
  [PseudoMetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]

omit [IsTopologicalGroup G] in
/-- Construct the path part of the original pair-chart interface from
literal quotient distance and locally bi-Lipschitz base coordinates.
Only the actual controlled pair lifts remain supplied geometry. -/
theorem original_pair_charts_of_controlled_lifts
    (coord : G ≃ₜ (Fin m → ℝ)) (hcoord : LocallyLipschitz coord)
    (hinv : LocallyLipschitz coord.symm) (K : Set G) (hK : IsCompact K)
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (b : Basis iota ℝ V.space) (M B r₀ : ℝ) (hB : 0 ≤ B) (hr₀ : 0 < r₀)
    (hlift : ∀ x y : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma, dist x y < r₀ →
      ∃ u v : ObservationGroup V, QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧
        u.base ∈ K ∧ v.base ∈ K ∧
        dist (b.equivFun u.obs) (b.equivFun v.obs) ≤ M * dist x y ∧
        dist u.base v.base ≤ B * dist x y) :
    ∃ A r : ℝ, 0 ≤ A ∧ 0 < r ∧ OriginalObservationPairCharts V Gamma b K M A r := by
  obtain ⟨A, s, hA, hs, hpath⟩ := compact_coordinate_short_paths coord hcoord hinv K hK
  have hden : 0 < B + 1 := by positivity
  refine ⟨A * B, min r₀ (s / (B + 1)), mul_nonneg hA hB,
    lt_min hr₀ (div_pos hs hden), ?_⟩
  intro x y hxy
  obtain ⟨u, v, hu, hv, huK, hvK, hcoeff, hbase⟩ :=
    hlift x y (hxy.trans_le (min_le_left _ _))
  have hnear : dist u.base v.base < s := by
    have h := (lt_div_iff₀ hden).mp (hxy.trans_le (min_le_right _ _))
    nlinarith [dist_nonneg (x := x) (y := y)]
  obtain ⟨p, hp⟩ := hpath u.base huK v.base hnear
  refine ⟨u, v, hu, hv, huK, hvK, hcoeff, p, ?_⟩
  intro z
  have hq := (quotient_mk_lipschitz_of_coset_formula Gamma hdist).dist_le_mul u.base (p z)
  have hx : observationQuotientBaseProjection V Gamma x = QuotientGroup.mk u.base := by
    rw [← hu]
    rfl
  rw [hx]
  simp only [NNReal.coe_one, one_mul] at hq
  exact (hq.trans (hp z)).trans
    ((mul_le_mul_of_nonneg_left hbase hA).trans_eq (by ring))

end GMZP0
