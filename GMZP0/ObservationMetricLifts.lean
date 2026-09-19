import GMZP0.CompactCosetLifts
import GMZP0.ObservationQuotientBorel
import GMZP0.CompactCoordinatePaths

/-! Construct the actual observation group's compact pair lifts. Metric
compatibility with its original product topology is explicit; compactness,
the covering cell and lift constants are derived internally. -/
noncomputable section
open Set Metric Module
namespace GMZP0
variable {G : Type*} [Group G] [PseudoMetricSpace G]
  (V : ObservationModule G) (Gamma : Subgroup G)
  {iota : Type*} [Fintype iota]
  [PseudoMetricSpace (ObservationGroup V)]
  [MetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]

local instance observationLiftMetricTopology : TopologicalSpace (ObservationGroup V) :=
  (inferInstance : PseudoMetricSpace (ObservationGroup V)).toUniformSpace.toTopologicalSpace

/-- The original closed base/fiber cell is compact for every supplied H
metric whose topology equals the original product topology. -/
theorem observation_metric_cell_compact
    (hcompat : observationLiftMetricTopology V = observationGroupTopology V)
    (K : Set G) (hK : IsCompact K) (b : Basis iota ℝ V.space) :
    IsCompact (observationGroupClosedCell V K b) := by
  rw [hcompat]
  exact observation_group_closedCell_compact V K hK b

variable [LocallyCompactSpace G]

/-- Local compactness for the supplied actual H metric follows from its
original product topology and finite-dimensional fiber. -/
theorem observation_metric_locallyCompact
    (hcompat : observationLiftMetricTopology V = observationGroupTopology V)
    (b : Basis iota ℝ V.space) : LocallyCompactSpace (ObservationGroup V) := by
  rw [hcompat]
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  exact observation_group_locallyCompact V

/-- Compact original base cover and actual compatible lattice bases
construct uniformly controlled pair lifts in H/Gamma_H. The fiber map is
the actual real-basis coefficient map, with no rounding of the observation. -/
theorem original_observation_controlled_pair_lifts
    (hcompat : observationLiftMetricTopology V = observationGroupTopology V)
    (K₀ : Set G) (hK₀ : IsCompact K₀)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K₀)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (b : Basis iota ℝ V.space)
    (hb : ∀ i, b i = (bZ i).val)
    (hfiber : LocallyLipschitz (fun a : ObservationGroup V => b.equivFun a.obs))
    (hbase : LocallyLipschitz (fun a : ObservationGroup V => a.base))
    (hdistH : ∀ a e : ObservationGroup V,
      dist (QuotientGroup.mk a : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)
        (QuotientGroup.mk e) = originalCosetInfDist (observationLatticeSubgroup V Gamma) a e) :
    ∃ K : Set G, IsCompact K ∧ ∃ M B r : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ 0 < r ∧
      ∀ x y : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma, dist x y < r →
        ∃ u v : ObservationGroup V, QuotientGroup.mk u = x ∧ QuotientGroup.mk v = y ∧
          u.base ∈ K ∧ v.base ∈ K ∧
          dist (b.equivFun u.obs) (b.equivFun v.obs) ≤ M * dist x y ∧
          dist u.base v.base ≤ B * dist x y := by
  let : LocallyCompactSpace (ObservationGroup V) := observation_metric_locallyCompact V hcompat b
  obtain ⟨E, hE, M, B, r, hM, hB, hr, hlift⟩ := compact_coset_coordinate_pair_lifts
    (observationLatticeSubgroup V Gamma) (observationGroupClosedCell V K₀ b)
    (observation_metric_cell_compact V hcompat K₀ hK₀ b)
    (observation_right_lattice_reduction V Gamma K₀ hcover bZ b hb) hdistH
    (fun a => b.equivFun a.obs) hfiber (fun a => a.base) hbase
  refine ⟨(fun a : ObservationGroup V => a.base) '' E, hE.image hbase.continuous,
    M, B, r, hM, hB, hr, ?_⟩
  intro x y hxy
  obtain ⟨u, v, huE, hvE, hu, hv, hcoeff, hbase'⟩ := hlift x y hxy
  exact ⟨u, v, hu, hv, ⟨u, huE, rfl⟩, ⟨v, hvE, rfl⟩, hcoeff, hbase'⟩

end GMZP0
