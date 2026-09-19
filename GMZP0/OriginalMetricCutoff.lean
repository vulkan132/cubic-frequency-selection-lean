import GMZP0.ObservationProjectionLipschitz

/-! Construct both original cutoff geometry inputs from literal compatible
metrics and locally Lipschitz actual coordinates. Pair lifts, short paths
and the global H-to-G projection constant are no longer supplied. -/
noncomputable section
open Set Metric Module
open scoped NNReal
namespace GMZP0
variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  (V : ObservationModule G) (Gamma : Subgroup G) [DiscreteTopology Gamma]
  {iota : Type*} [Fintype iota] {m : ℕ}
  [PseudoMetricSpace (ObservationGroup V)] [MetricSpace (G ⧸ Gamma)]
  [MetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]

local instance originalCutoffHMetricTopology : TopologicalSpace (ObservationGroup V) :=
  (inferInstance : PseudoMetricSpace (ObservationGroup V)).toUniformSpace.toTopologicalSpace

/-- One actual global projection constant and one original cutoff constant
are internally constructed before every positive scale. The literal
metric formulas and coordinate regularity remain explicit geometric inputs. -/
theorem original_observation_metric_cutoff
    (coord : G ≃ₜ (Fin m → ℝ)) (hcoord : LocallyLipschitz coord)
    (hinv : LocallyLipschitz coord.symm)
    (hcompat : originalCutoffHMetricTopology V = observationGroupTopology V)
    (K₀ : Set G) (hK₀ : IsCompact K₀)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K₀)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (b : Basis iota ℝ V.space)
    (hb : ∀ i, b i = (bZ i).val)
    (hfiber : LocallyLipschitz (fun a : ObservationGroup V => b.equivFun a.obs))
    (hbase : LocallyLipschitz (fun a : ObservationGroup V => a.base))
    (hdistG : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (hdistH : ∀ a e : ObservationGroup V,
      dist (QuotientGroup.mk a : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)
        (QuotientGroup.mk e) = originalCosetInfDist (observationLatticeSubgroup V Gamma) a e)
    (D : Set G) (hD : IsCompact (closure D))
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D) :
    ∃ J : ℝ≥0, LipschitzWith J (observationQuotientBaseProjection V Gamma) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
        LipschitzWith (Real.toNNReal (L / t)) (fun x =>
          (boundaryCutoff (QuotientGroup.mk '' frontier D) t
            (observationQuotientBaseProjection V Gamma x) : ℂ) * quotientObservation V c x) := by
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  obtain ⟨K, hK, M, B, r, hM, hB, hr, hlift⟩ := original_observation_controlled_pair_lifts
    V Gamma hcompat K₀ hK₀ hcover bZ b hb hfiber hbase hdistH
  obtain ⟨J, hJ⟩ := original_projection_lipschitz_of_lifts V Gamma K₀ hK₀ hcover hdistG B r hB hr
    (fun x y hxy => by
      obtain ⟨u, v, hu, hv, _, _, _, hbase'⟩ := hlift x y hxy
      exact ⟨u, v, hu, hv, hbase'⟩)
  obtain ⟨A, s, hA, hs, hpairs⟩ := original_pair_charts_of_controlled_lifts V Gamma
    coord hcoord hinv K hK hdistG b M B r hB hr hlift
  exact ⟨J, hJ, original_observation_cutoff_lipschitz_of_charts V Gamma
    D K hK hD huniq c hc b M A s hM hA hs hpairs J hJ⟩

end GMZP0
