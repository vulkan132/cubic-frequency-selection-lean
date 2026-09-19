import GMZP0.QuotientCountingLift

/-! Uniqueness of invariant probability on the original compact quotient.
The lattice may be nonnormal. Counting lifts and ambient Haar uniqueness
identify the measures without changing any original observation section. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [PolishSpace G] [LocallyCompactSpace G]

/-- A bounded measurable right inverse of the actual quotient map is constructed internally. -/
theorem compact_quotient_bounded_section (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] :
    ∃ (K : Set G) (s : G ⧸ Gamma → G), IsCompact K ∧ Measurable s ∧
      Function.RightInverse s (QuotientGroup.mk : G → G ⧸ Gamma) ∧ ∀ x, s x ∈ K := by
  obtain ⟨K, c, hK, hc, hbound⟩ := observation_compact_measurable_section_exists Gamma
  refine ⟨K, observationQuotientSection c, hK, observationQuotientSection_measurable c hc,
    observationQuotientSection_rightInverse c, ?_⟩
  intro x
  induction x using Quotient.inductionOn with
  | h g => exact hbound ⟨g, rfl⟩

/-- Every two full-group invariant probabilities on the actual compact discrete quotient coincide. -/
theorem compact_quotient_invariant_probability_unique (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)]
    (mu nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [SMulInvariantMeasure G (G ⧸ Gamma) mu] [SMulInvariantMeasure G (G ⧸ Gamma) nu] : mu = nu := by
  let : Countable Gamma := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  let : T2Space (G ⧸ Gamma) := inferInstance
  let : BorelSpace (G ⧸ Gamma) := CosetSpace.borelSpace
  obtain ⟨K, s, hK, hs, hright, hbound⟩ := compact_quotient_bounded_section Gamma
  let M := quotientCountingLift Gamma s mu
  let N := quotientCountingLift Gamma s nu
  let : IsMulLeftInvariant M := quotient_countingLift_leftInvariant Gamma s hs hright mu
  let : IsMulLeftInvariant N := quotient_countingLift_leftInvariant Gamma s hs hright nu
  let : IsFiniteMeasureOnCompacts M := quotient_countingLift_finite_compacts Gamma s hs K hK hbound mu
  let : IsFiniteMeasureOnCompacts N := quotient_countingLift_finite_compacts Gamma s hs K hK hbound nu
  let lam : Measure G := Measure.haar
  let D := quotientSectionDomain Gamma s
  have hDK : D ⊆ K := by
    intro g hg
    have h := hbound (QuotientGroup.mk g)
    change s (QuotientGroup.mk g) = g at hg
    rwa [hg] at h
  have hfin : lam D ≠ ∞ := (lt_of_le_of_lt (measure_mono hDK) hK.measure_lt_top).ne
  have hM : M = haarScalarFactor M lam • lam := isMulLeftInvariant_eq_smul M lam
  have hN : N = haarScalarFactor N lam • lam := isMulLeftInvariant_eq_smul N lam
  have hm : M D = 1 := (quotient_countingLift_domain_mass Gamma s hs hright mu).trans (measure_univ)
  have hn : N D = 1 := (quotient_countingLift_domain_mass Gamma s hs hright nu).trans (measure_univ)
  rw [hM, Measure.smul_apply] at hm
  rw [hN, Measure.smul_apply] at hn
  change (haarScalarFactor M lam : ℝ≥0∞) * lam D = 1 at hm
  change (haarScalarFactor N lam : ℝ≥0∞) * lam D = 1 at hn
  have hpos : lam D ≠ 0 := by
    intro hzero
    simp only [hzero, mul_zero, zero_ne_one] at hm
  have hcoef : haarScalarFactor M lam = haarScalarFactor N lam :=
    ENNReal.coe_injective ((ENNReal.mul_left_inj hpos hfin).mp (hm.trans hn.symm))
  have he : M = N := by rw [hM, hN, hcoef]
  calc
    mu = (M.restrict D).map QuotientGroup.mk := (quotient_countingLift_recover Gamma s hs hright mu).symm
    _ = (N.restrict D).map QuotientGroup.mk := congrArg (fun q : Measure G => (q.restrict D).map QuotientGroup.mk) he
    _ = nu := quotient_countingLift_recover Gamma s hs hright nu

end GMZP0
