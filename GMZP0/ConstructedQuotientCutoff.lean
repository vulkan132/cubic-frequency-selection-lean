import GMZP0.OriginalCosetMetric
import GMZP0.ObservationLatticeClosed
import GMZP0.OriginalMetricCutoff

/-! Construct both actual quotient metrics inside the original cutoff
theorem. Source metrics with isometric original right lattice actions and
locally Lipschitz original coordinates remain explicit internal inputs. -/
noncomputable section
open Set Metric Module
open scoped NNReal
namespace GMZP0
variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  (V : ObservationModule G) (Gamma : Subgroup G) [DiscreteTopology Gamma]
  {iota : Type*} [Fintype iota] {m : ℕ}
  [PseudoMetricSpace (ObservationGroup V)]

local instance constructedHMetricTopology : TopologicalSpace (ObservationGroup V) :=
  (inferInstance : PseudoMetricSpace (ObservationGroup V)).toUniformSpace.toTopologicalSpace

/-- The actual quotient metrics, their formulas and topology agreement,
the global projection constant, and the original C/t cutoff bound are
constructed. No independent quotient metric or distance formula is supplied. -/
theorem original_observation_cutoff_from_isometric_actions
    (coord : G ≃ₜ (Fin m → ℝ)) (hcoord : LocallyLipschitz coord)
    (hinv : LocallyLipschitz coord.symm)
    (hcompat : constructedHMetricTopology V = observationGroupTopology V)
    (hrightG : ∀ a : Gamma, Isometry (fun x : G => x * a))
    (hrightH : ∀ a : observationLatticeSubgroup V Gamma,
      Isometry (fun x : ObservationGroup V => x * a))
    (K₀ : Set G) (hK₀ : IsCompact K₀)
    (hcover : ∀ g : G, ∃ gamma : Gamma, g * gamma ∈ K₀)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (b : Basis iota ℝ V.space)
    (hb : ∀ i, b i = (bZ i).val)
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u))
    (hfiber : LocallyLipschitz (fun a : ObservationGroup V => b.equivFun a.obs))
    (hbase : LocallyLipschitz (fun a : ObservationGroup V => a.base))
    (D : Set G) (hD : IsCompact (closure D))
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D) :
    ∃ mG : MetricSpace (G ⧸ Gamma),
      ∃ mH : MetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
        mG.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Gamma ∧
        mH.toUniformSpace.toTopologicalSpace = TopologicalSpace.coinduced
          (QuotientGroup.mk : ObservationGroup V →
            ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) (observationGroupTopology V) ∧
        (letI := mG
         letI := mH
         (∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
           originalCosetInfDist Gamma g h) ∧
         (∀ u v : ObservationGroup V,
           dist (QuotientGroup.mk u : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)
             (QuotientGroup.mk v) = originalCosetInfDist (observationLatticeSubgroup V Gamma) u v) ∧
         ∃ J : ℝ≥0, LipschitzWith J (observationQuotientBaseProjection V Gamma) ∧
           ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
             LipschitzWith (Real.toNNReal (L / t)) (fun x =>
               (boundaryCutoff (QuotientGroup.mk '' frontier D) t
                 (observationQuotientBaseProjection V Gamma x) : ℂ) * quotientObservation V c x)) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  let : IsTopologicalGroup (ObservationGroup V) := by
    rw [hcompat]
    exact observation_isTopologicalGroup V hcont
  have hclosedG : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  have hclosedH : IsClosed (observationLatticeSubgroup V Gamma : Set (ObservationGroup V)) := by
    rw [hcompat]
    exact observation_lattice_closed_by_values V Gamma hclosedG
  let mG := originalCosetMetric Gamma hclosedG hrightG K₀ hK₀ hcover
  let mH := originalCosetMetric (observationLatticeSubgroup V Gamma) hclosedH hrightH
    (observationGroupClosedCell V K₀ b) (observation_metric_cell_compact V hcompat K₀ hK₀ b)
    (observation_right_lattice_reduction V Gamma K₀ hcover bZ b hb)
  refine ⟨mG, mH, rfl, ?_, ?_⟩
  · change TopologicalSpace.coinduced
      (QuotientGroup.mk : ObservationGroup V →
        ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) (constructedHMetricTopology V) = _
    rw [hcompat]
  · let := mG
    let := mH
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    exact original_observation_metric_cutoff V Gamma coord hcoord hinv hcompat K₀ hK₀ hcover
      bZ b hb hfiber hbase (fun _ _ => rfl) (fun _ _ => rfl) D hD huniq c hc

end GMZP0
