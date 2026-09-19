import GMZP0.ObservationSourceMetrics
import GMZP0.OriginalCosetMetric
import GMZP0.ObservationLatticeClosed
import GMZP0.OriginalMetricBoundaryOrbit

/-! Assemble the original polynomial data, actual H source metrics and
original quotient metrics into the full original orbit forcing theorem.
No metric, coordinate regularity or geometric cutoff estimate is supplied. -/
noncomputable section
open Set Metric Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
universe uI
variable {G iota : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Fintype iota] {m : ℕ}

/-- One actual original quotient metric precedes every specified original
section in the same cell, invariant probabilities, correlation threshold,
full finite orbit and N. The original N normalization is retained. -/
theorem original_polynomial_boundary_nonequidistribution
    (V : ObservationModule G) (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℝ)
    (hjoint : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u s, coord (g * u) s = coord u s + MvPolynomial.aeval (coord u) (q g s))
    (hlow : ∀ g s d, d ∈ (q g s).support → ∀ j ∈ d.support, j.val < s.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hgrid : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (b : Basis iota ℝ V.space)
    (hb : ∀ i, b i = (bZ i).val) (P : iota → MvPolynomial (Fin m) ℝ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (a : Fin m → ℝ) :
    ∃ mQ : MetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
      mQ.toUniformSpace.toTopologicalSpace =
        QuotientGroup.instTopologicalSpace (observationLatticeSubgroup V Gamma) ∧
      (letI := mQ
       ∀ (c : ObservationSection Gamma),
         Set.range c.representative ⊆ coordinateHalfOpenCell coord a →
       ∀ (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
         [IsProbabilityMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu],
       ∀ (nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure nu] [SMulInvariantMeasure G _ nu],
       ∀ gamma : ℝ, 0 < gamma →
         ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
           (∀ (I : Type uI) [Fintype I]
             (u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
             gamma < ‖complexUniformMean (fun i => quotientObservation V c (u i))‖ →
               ¬ LipschitzOrbitDiscrepancy mu u alpha) ∧
           (∀ N : ℕ, 0 < N → ∀ (I : Type uI) [Fintype I], Fintype.card I ≤ N →
             ∀ u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma,
               gamma < ‖(∑ i, quotientObservation V c (u i)) / (N : ℂ)‖ →
                 gamma * (N : ℝ) < Fintype.card I ∧ ¬ LipschitzOrbitDiscrepancy mu u alpha)) := by
  obtain ⟨rawG, rawH, htG, htH, hrG, hrH, hcG, hiG, hbase, hfiber⟩ :=
    original_observation_source_metrics V coord b p hjoint P hP
  let mG := @MetricSpace.replaceTopology G (inferInstance : TopologicalSpace G) rawG htG.symm
  let mH := @MetricSpace.replaceTopology (ObservationGroup V) (observationGroupTopology V) rawH htH.symm
  have heG : mG = rawG := MetricSpace.replaceTopology_eq _ _
  have heH : mH = rawH := MetricSpace.replaceTopology_eq _ _
  have hrG' : ∀ g : G, Isometry (fun x : G => x * g) := by
    change ∀ g : G, @Isometry G G mG.toPseudoEMetricSpace mG.toPseudoEMetricSpace (fun x => x * g)
    rw [heG]
    exact hrG
  have hrH' : ∀ h : ObservationGroup V, Isometry (fun x : ObservationGroup V => x * h) := by
    change ∀ h, @Isometry (ObservationGroup V) (ObservationGroup V)
      mH.toPseudoEMetricSpace mH.toPseudoEMetricSpace (fun x => x * h)
    rw [heH]
    exact hrH
  have hcG' : LocallyLipschitz coord := by
    change @LocallyLipschitz G (Fin m → ℝ) mG.toPseudoEMetricSpace inferInstance coord
    rw [heG]
    exact hcG
  have hiG' : LocallyLipschitz coord.symm := by
    change @LocallyLipschitz (Fin m → ℝ) G inferInstance mG.toPseudoEMetricSpace coord.symm
    rw [heG]
    exact hiG
  have hbase' : LocallyLipschitz (fun x : ObservationGroup V => x.base) := by
    change @LocallyLipschitz (ObservationGroup V) G mH.toPseudoEMetricSpace mG.toPseudoEMetricSpace _
    rw [heH, heG]
    exact hbase
  have hfiber' : LocallyLipschitz (fun x : ObservationGroup V => b.equivFun x.obs) := by
    change @LocallyLipschitz (ObservationGroup V) (iota → ℝ) mH.toPseudoEMetricSpace inferInstance _
    rw [heH]
    exact hfiber
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hcont := observation_basis_polynomials_continuous V coord b P hP
  let : IsTopologicalGroup (ObservationGroup V) := observation_isTopologicalGroup V hcont
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  let : BorelSpace (G ⧸ Gamma) := CosetSpace.borelSpace
  have hclosedG : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  have hclosedH := observation_lattice_closed_by_values V Gamma hclosedG
  have hK := coordinate_half_open_cell_compact_closure coord a
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q htri hlow hint hgrid a
  have hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ closure (coordinateHalfOpenCell coord a) := by
    intro g
    obtain ⟨gamma, hgamma⟩ := (huniq g).exists
    exact ⟨gamma, subset_closure hgamma⟩
  let mQG := originalCosetMetric Gamma hclosedG (fun gamma => hrG' gamma)
    (closure (coordinateHalfOpenCell coord a)) hK hcover
  let mQH := originalCosetMetric (observationLatticeSubgroup V Gamma) hclosedH
    (fun lambda => hrH' lambda)
    (observationGroupClosedCell V (closure (coordinateHalfOpenCell coord a)) b)
    (observation_metric_cell_compact V rfl _ hK b)
    (observation_right_lattice_reduction V Gamma _ hcover bZ b hb)
  refine ⟨mQH, rfl, ?_⟩
  intro c hc mu hmu hinvMu nu hnu hinvNu gamma hgamma
  let := hmu
  let := hinvMu
  let := hnu
  let := hinvNu
  exact original_metric_boundary_nonequidistribution V Gamma coord hcG' hiG'
    q htri hlow hint hgrid rfl bZ b hb hfiber' hbase' (fun _ _ => rfl) (fun _ _ => rfl)
    hcont h1 a c hc mu nu gamma hgamma

end GMZP0
