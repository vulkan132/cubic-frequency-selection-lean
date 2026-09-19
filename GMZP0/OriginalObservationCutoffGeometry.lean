import GMZP0.ObservationBranchEstimate
import GMZP0.BoundaryCutoffGluing
import GMZP0.OriginalBoundaryOrbit
import Mathlib.Topology.Path

/-! Original compact-chart geometry implies the missing O(1/t) Lipschitz
estimate for the actual cutoff observation. The chart lifts and path bounds
are explicit metric construction obligations, not external deep theorems. -/
noncomputable section
open Set Metric Module
open scoped NNReal
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : ObservationModule G) (Gamma : Subgroup G)
  {iota : Type*} [Fintype iota]
  [PseudoMetricSpace (G ⧸ Gamma)]
  [PseudoMetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]

/-- Nearby original quotient points admit representatives with compact
base coordinates, controlled actual fiber coefficient differences, and a
base path of controlled projected radius. Every constant precedes the pair.
The path need not stay inside the chosen fundamental domain. -/
def OriginalObservationPairCharts (b : Basis iota ℝ V.space) (K : Set G)
    (M A r : ℝ) : Prop :=
  ∀ x y : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma, dist x y < r →
    ∃ u v : ObservationGroup V,
      QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧ u.base ∈ K ∧ v.base ∈ K ∧
      dist (b.equivFun u.obs) (b.equivFun v.obs) ≤ M * dist x y ∧
      ∃ p : Path u.base v.base, ∀ s,
        dist (observationQuotientBaseProjection V Gamma x) (QuotientGroup.mk (p s)) ≤ A * dist x y

variable [T2Space G] [DiscreteTopology Gamma]

/-- The unchanged original observation satisfies a uniform local
alternative. Same corrections use the actual finite evaluation bound;
different corrections force the actual base boundary within A*distance. -/
theorem original_observation_local_alternative
    (D K : Set G) (hK : IsCompact K) (hD : IsCompact (closure D))
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    (b : Basis iota ℝ V.space) (M A r : ℝ) (hM : 0 ≤ M)
    (hpairs : OriginalObservationPairCharts V Gamma b K M A r) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, dist x y < r →
      ‖quotientObservation V c x - quotientObservation V c y‖ ≤ L * dist x y ∨
        ((QuotientGroup.mk '' frontier D : Set (G ⧸ Gamma)).Nonempty ∧
          infDist (observationQuotientBaseProjection V Gamma x) (QuotientGroup.mk '' frontier D) ≤
            A * dist x y) := by
  obtain ⟨C, hC, hbranch⟩ := original_observation_same_correction_bound V Gamma c
    K (closure D) hK hD (hc.trans subset_closure) b
  refine ⟨C * M, mul_nonneg hC hM, ?_⟩
  intro x y hxy
  obtain ⟨u, v, hu, hv, huK, hvK, hcoeff, p, hp⟩ := hpairs x y hxy
  by_cases heq : observationCorrection c u.base = observationCorrection c v.base
  · left
    calc
      ‖quotientObservation V c x - quotientObservation V c y‖ =
          ‖quotientObservation V c (QuotientGroup.mk u) -
            quotientObservation V c (QuotientGroup.mk v)‖ := by rw [hu, hv]
      _ ≤ C * dist (b.equivFun u.obs) (b.equivFun v.obs) := hbranch u v huK hvK heq
      _ ≤ (C * M) * dist x y := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcoeff hC
  · right
    have hp0 : (QuotientGroup.mk (p 0) : G ⧸ Gamma) = observationQuotientBaseProjection V Gamma x := by
      rw [p.source, ← hu]
      rfl
    have h := original_correction_change_boundary_distance Gamma D huniq c hc
      p p.continuous 0 1 (by simpa only [p.source, p.target] using heq)
      (A * dist x y) (fun s => by rw [hp0]; exact hp s)
    simpa only [hp0] using h

/-- One structural constant precedes every cutoff scale. The actual
observation, original section and periodic quotient representatives are
unchanged; no Lipschitz hypothesis on the final product is supplied. -/
theorem original_observation_cutoff_lipschitz_of_charts
    (D K : Set G) (hK : IsCompact K) (hD : IsCompact (closure D))
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    (b : Basis iota ℝ V.space) (M A r : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hr : 0 < r)
    (hpairs : OriginalObservationPairCharts V Gamma b K M A r)
    (J : ℝ≥0) (hpi : LipschitzWith J (observationQuotientBaseProjection V Gamma)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      LipschitzWith (Real.toNNReal (B / t)) (fun x =>
        (boundaryCutoff (QuotientGroup.mk '' frontier D) t
          (observationQuotientBaseProjection V Gamma x) : ℂ) * quotientObservation V c x) := by
  obtain ⟨L, hL, hlocal⟩ := original_observation_local_alternative V Gamma
    D K hK hD huniq c hc b M A r hM hpairs
  refine ⟨L + 2 * A + J + 2 / r, by positivity, ?_⟩
  intro t ht ht1
  exact boundary_cutoff_lipschitz_of_local_alternative
    (observationQuotientBaseProjection V Gamma) J hpi (QuotientGroup.mk '' frontier D)
    (quotientObservation V c) (quotient_observation_norm V c) L A r hL hA hr hlocal ht ht1

local instance cutoffGeometryMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : PseudoMetricSpace (G ⧸ Gamma)).toUniformSpace.toTopologicalSpace

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [BorelSpace (G ⧸ Gamma)] [FiniteDimensional ℝ V.space]

/-- The compact-chart construction replaces the product-Lipschitz premise
in the original orbit theorem. The original zero mean is still derived
internally and the scales precede every finite orbit and orbit length. -/
theorem original_boundary_nonequidistribution_of_charts
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (D K : Set G) (hK : IsCompact K) (hD : IsCompact (closure D))
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    (hcmeas : Measurable c.representative)
    (b : Basis iota ℝ V.space) (M A r : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hr : 0 < r)
    (hpairs : OriginalObservationPairCharts V Gamma b K M A r)
    (J : ℝ≥0) (hpi : LipschitzWith J (observationQuotientBaseProjection V Gamma))
    (mu : MeasureTheory.Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.SMulInvariantMeasure (ObservationGroup V) _ mu]
    (nu : MeasureTheory.Measure (G ⧸ Gamma)) [MeasureTheory.IsProbabilityMeasure nu]
    (hp : MeasureTheory.MeasurePreserving (observationQuotientBaseProjection V Gamma) mu nu)
    (C : ℝ) (hC : 0 ≤ C)
    (hmass : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (nu (boundaryTube (QuotientGroup.mk '' frontier D) (2 * t))).toReal ≤ C * t)
    (gamma : ℝ) (hg : 0 < gamma) :
    ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
      ∀ (I : Type*) [Fintype I]
        (u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
        gamma < ‖complexUniformMean (fun i => quotientObservation V c (u i))‖ →
          ¬ LipschitzOrbitDiscrepancy mu u alpha := by
  obtain ⟨B, hB, hcut⟩ := original_observation_cutoff_lipschitz_of_charts V Gamma
    D K hK hD huniq c hc b M A r hM hA hr hpairs J hpi
  exact original_boundary_nonequidistribution V Gamma hcont h1 c hcmeas mu nu hp J hpi
    (QuotientGroup.mk '' frontier D) C B hC hB hmass hcut gamma hg

end GMZP0
