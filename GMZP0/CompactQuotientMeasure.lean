import GMZP0.ObservationBoundedSection
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! An invariant probability on the actual compact discrete quotient.
Right invariance of ambient Haar is proved from a bounded strict domain,
rather than assumed. No normality of the lattice is used. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Pointwise ENNReal
namespace GMZP0

/-- Inversion exchanges strict right correction domains and strict left correction domains. -/
theorem strict_right_domain_inverse {G : Type*} [Group G] (Gamma : Subgroup G)
    (S : Set G) (hS : ∀ x : G, ∃! gamma : Gamma, x * gamma ∈ S) :
    ∀ x : G, ∃! gamma : Gamma, (gamma : G) * x ∈ S⁻¹ := by
  intro x
  obtain ⟨gamma, hgamma, huniq⟩ := hS x⁻¹
  refine ⟨gamma⁻¹, ?_, ?_⟩
  · simpa only [Set.mem_inv, mul_inv_rev, Subgroup.coe_inv, inv_inv] using hgamma
  · intro delta hdelta
    have hd : delta⁻¹ = gamma := huniq delta⁻¹ (by
      simpa only [Set.mem_inv, mul_inv_rev, Subgroup.coe_inv] using hdelta)
    exact inv_injective (by simpa only [inv_inv] using hd)

/-- Right preimages preserve every strict left correction, pointwise. -/
theorem strict_left_domain_right_preimage {G : Type*} [Group G] (Gamma : Subgroup G)
    (S : Set G) (hS : ∀ x : G, ∃! gamma : Gamma, (gamma : G) * x ∈ S) (g : G) :
    ∀ x : G, ∃! gamma : Gamma, (gamma : G) * x ∈ (fun y => y * g) ⁻¹' S := by
  intro x
  simpa only [Set.mem_preimage, mul_assoc] using hS (x * g)

section Haar
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [PolishSpace G] [LocallyCompactSpace G]

/-- A compactly contained strict lattice domain forces right invariance of every ambient Haar measure.
The finite positive domain mass cancels the Haar scaling factor. -/
theorem haar_right_invariant_of_compact_left_domain (Gamma : Subgroup G) [Countable Gamma]
    (nu : Measure G) [IsHaarMeasure nu] (S : Set G) (hS : MeasurableSet S)
    (hK : IsCompact (closure S))
    (hunique : ∀ x : G, ∃! gamma : Gamma, (gamma : G) * x ∈ S) :
    IsMulRightInvariant nu := by
  have hfund : IsFundamentalDomain Gamma S nu := IsFundamentalDomain.mk' hS.nullMeasurableSet hunique
  have hpos : nu S ≠ 0 := hfund.measure_ne_zero (NeZero.ne nu)
  have hfin : nu S ≠ ∞ := (lt_of_le_of_lt (measure_mono subset_closure) hK.measure_lt_top).ne
  constructor
  intro g
  have hfund' : IsFundamentalDomain Gamma ((fun y : G => y * g) ⁻¹' S) nu :=
    IsFundamentalDomain.mk' (hS.preimage (measurable_id.mul_const g)).nullMeasurableSet
      (strict_left_domain_right_preimage Gamma S hunique g)
  have hmass : nu.map (fun y => y * g) S = nu S := by
    rw [Measure.map_apply (continuous_mul_const g).measurable hS]
    exact hfund'.measure_eq hfund
  have hscale := isMulLeftInvariant_eq_smul (nu.map (fun y => y * g)) nu
  have hcoeff : haarScalarFactor (nu.map (fun y => y * g)) nu = 1 := by
    rw [hscale, Measure.smul_apply] at hmass
    change (haarScalarFactor (nu.map (fun y => y * g)) nu : ℝ≥0∞) * nu S = nu S at hmass
    have hm : (haarScalarFactor (nu.map (fun y => y * g)) nu : ℝ≥0∞) * nu S = 1 * nu S := by
      simpa only [one_mul] using hmass
    exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos hfin).mp hm)
  simpa only [hcoeff, one_smul] using hscale

/-- Discreteness and compactness of the original quotient imply ambient Haar right invariance. -/
theorem cocompact_lattice_haar_right_invariant (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] (nu : Measure G) [IsHaarMeasure nu] :
    IsMulRightInvariant nu := by
  let : Countable Gamma := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨S, hS, hK, huniq⟩ := observation_borel_fundamental_domain_exists Gamma
  apply haar_right_invariant_of_compact_left_domain Gamma nu S⁻¹ hS.inv
  · simpa only [inv_closure] using hK.inv
  · exact strict_right_domain_inverse Gamma S huniq

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [PolishSpace G]
  [LocallyCompactSpace G] in
/-- A strict right correction domain is a fundamental domain for the actual opposite subgroup action. -/
theorem strict_right_domain_fundamental (Gamma : Subgroup G) (nu : Measure G)
    (S : Set G) (hS : MeasurableSet S)
    (hunique : ∀ x : G, ∃! gamma : Gamma, x * gamma ∈ S) :
    IsFundamentalDomain Gamma.op S nu := by
  apply IsFundamentalDomain.mk' hS.nullMeasurableSet
  intro x
  obtain ⟨gamma, hgamma, huniq⟩ := hunique x
  refine ⟨⟨MulOpposite.op (gamma : G), gamma.property⟩, hgamma, ?_⟩
  intro delta hdelta
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact congrArg Subtype.val (huniq ⟨MulOpposite.unop delta.val, delta.property⟩ hdelta)

/-- Construct a probability measure invariant under the full group on its original compact quotient.
Ambient Haar right invariance, finite positive domain mass and normalization are proved internally. -/
theorem compact_quotient_invariant_probability (Gamma : Subgroup G)
    [DiscreteTopology Gamma] [CompactSpace (G ⧸ Gamma)] :
    ∃ mu : Measure (G ⧸ Gamma), IsProbabilityMeasure mu ∧ SMulInvariantMeasure G (G ⧸ Gamma) mu := by
  let : Countable Gamma := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  let : T2Space (G ⧸ Gamma) := inferInstance
  let nu : Measure G := Measure.haar
  let : IsMulRightInvariant nu := cocompact_lattice_haar_right_invariant Gamma nu
  obtain ⟨S, hS, hK, huniq⟩ := observation_borel_fundamental_domain_exists Gamma
  have hfund := strict_right_domain_fundamental Gamma nu S hS huniq
  have hpos : nu S ≠ 0 := hfund.measure_ne_zero (NeZero.ne nu)
  have hfin : nu S ≠ ∞ := (lt_of_le_of_lt (measure_mono subset_closure) hK.measure_lt_top).ne
  let : IsFiniteMeasure (nu.restrict S) := isFiniteMeasure_restrict.mpr hfin
  let mu : Measure (G ⧸ Gamma) := (nu.restrict S).map QuotientGroup.mk
  let : HasFundamentalDomain Gamma.op G nu := ⟨S, hfund⟩
  let : QuotientMeasureEqMeasurePreimage nu mu := hfund.quotientMeasureEqMeasurePreimage_quotientMeasure
  let : SMulInvariantMeasure G (G ⧸ Gamma) mu :=
    QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient nu
  have hmass : mu Set.univ = nu S := by
    simp only [mu, Measure.map_apply QuotientGroup.measurable_coe MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  let : NeZero mu := ⟨fun h => hpos (by simpa [h] using hmass.symm)⟩
  exact ⟨(mu Set.univ)⁻¹ • mu, inferInstance, inferInstance⟩

end Haar
end GMZP0
