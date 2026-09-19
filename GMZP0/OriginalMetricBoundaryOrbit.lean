import GMZP0.OriginalMetricCutoff
import GMZP0.CanonicalObservationSection
import GMZP0.ObservationMeasureProjection
import GMZP0.OrbitIntervalNormalization

/-! Assemble actual coordinate measure, compact pair lifts, cutoff
geometry, mean zero and orbit testing. All geometric bounds are derived
from literal metric and coordinate inputs, which remain to be constructed
from the complete original Malcev/Lie presentation. -/
noncomputable section
open Set Metric Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
universe uI
variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (V : ObservationModule G) (Gamma : Subgroup G) [DiscreteTopology Gamma]
  {iota : Type*} [Fintype iota] {m : ℕ}
  [PseudoMetricSpace (ObservationGroup V)] [MetricSpace (G ⧸ Gamma)]
  [MetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]

local instance assembledHMetricTopology : TopologicalSpace (ObservationGroup V) :=
  (inferInstance : PseudoMetricSpace (ObservationGroup V)).toUniformSpace.toTopologicalSpace
local instance assembledBaseMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : MetricSpace (G ⧸ Gamma)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

variable [BorelSpace (G ⧸ Gamma)]

/-- One scale and tolerance precede every finite original orbit. Actual
tube mass, pair lifts, short paths, projection Lipschitz bound, original
cutoff regularity, section measurability, measure projection and zero mean
are all derived internally. No quantitative Leibman conclusion is claimed. -/
theorem original_metric_boundary_nonequidistribution
    (coord : G ≃ₜ (Fin m → ℝ)) (hcoord : LocallyLipschitz coord)
    (hinv : LocallyLipschitz coord.symm)
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hgroup : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hgrid : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (hcompat : assembledHMetricTopology V = observationGroupTopology V)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (b : Basis iota ℝ V.space)
    (hb : ∀ i, b i = (bZ i).val)
    (hfiber : LocallyLipschitz (fun a : ObservationGroup V => b.equivFun a.obs))
    (hbase : LocallyLipschitz (fun a : ObservationGroup V => a.base))
    (hdistG : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (hdistH : ∀ a e : ObservationGroup V,
      dist (QuotientGroup.mk a : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)
        (QuotientGroup.mk e) = originalCosetInfDist (observationLatticeSubgroup V Gamma) a e)
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (a : Fin m → ℝ) (c : ObservationSection Gamma)
    (hc : Set.range c.representative ⊆ coordinateHalfOpenCell coord a)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsProbabilityMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu]
    (nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure nu] [SMulInvariantMeasure G _ nu]
    (gamma : ℝ) (hg : 0 < gamma) :
    ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
      (∀ (I : Type uI) [Fintype I]
        (u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
        gamma < ‖complexUniformMean (fun i => quotientObservation V c (u i))‖ →
          ¬ LipschitzOrbitDiscrepancy mu u alpha) ∧
      (∀ (N : ℕ), 0 < N → ∀ (I : Type uI) [Fintype I], Fintype.card I ≤ N →
        ∀ u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma,
          gamma < ‖(∑ i, quotientObservation V c (u i)) / (N : ℂ)‖ →
            gamma * (N : ℝ) < Fintype.card I ∧ ¬ LipschitzOrbitDiscrepancy mu u alpha) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  let hQ := (canonical_coordinate_section Gamma coord q hgroup hlow hint hgrid a).1
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q hgroup hlow hint hgrid a
  have hK := coordinate_half_open_cell_compact_closure coord a
  have hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ closure (coordinateHalfOpenCell coord a) := by
    intro g
    obtain ⟨gamma, hgamma⟩ := (huniq g).exists
    exact ⟨gamma, subset_closure hgamma⟩
  obtain ⟨J, hJ, L, hL, hcut⟩ := original_observation_metric_cutoff V Gamma
    coord hcoord hinv hcompat (closure (coordinateHalfOpenCell coord a)) hK hcover
    bZ b hb hfiber hbase hdistG hdistH (coordinateHalfOpenCell coord a) hK huniq c hc
  obtain ⟨C, hC, hmass⟩ := original_quotient_face_tube_linear_of_locallyLipschitz
    Gamma coord q hgroup hlow hint hgrid a hdistG hcoord
  have hcmeas := specified_canonical_coordinate_section_measurable
    Gamma coord q hgroup hlow hint hgrid a c hc
  have hp := observation_base_projection_measurePreserving V Gamma mu nu
  have hmass' : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (nu (boundaryTube (originalCellFaceImage Gamma coord a) (2 * t))).toReal ≤ (2 * C) * t := by
    intro t ht _
    have h := hmass nu inferInstance inferInstance (2 * t) (by positivity)
    convert h using 1
    ring
  obtain ⟨t, alpha, ht, ht1, ha, hforce⟩ := original_boundary_nonequidistribution
    V Gamma hcont h1 c hcmeas mu nu hp J hJ (originalCellFaceImage Gamma coord a)
    (2 * C) L (by positivity) hL hmass' hcut gamma hg
  exact ⟨t, alpha, ht, ht1, ha, hforce, N_normalized_orbit_forcing mu (quotientObservation V c)
    (fun x => (quotient_observation_norm V c x).le) gamma alpha hg hforce⟩

end GMZP0
