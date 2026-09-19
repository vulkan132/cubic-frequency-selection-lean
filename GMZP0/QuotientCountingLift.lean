import GMZP0.CompactQuotientMeasure

/-! Lift a measure on the actual coset quotient by counting its original
lattice fibers. Bounded measurable sections are auxiliary to the measure
construction and do not replace the section in the original observation. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Pointwise ENNReal BigOperators
namespace GMZP0
variable {G : Type*} [Group G]

/-- The chosen original representative, as a function on the actual quotient. -/
def observationQuotientSection {Gamma : Subgroup G} (c : ObservationSection Gamma) : G ⧸ Gamma → G :=
  Quotient.lift c.representative (by
    intro a b hab
    have hgamma : a⁻¹ * b ∈ Gamma := QuotientGroup.leftRel_apply.mp hab
    have h := c.right_invariant a ⟨a⁻¹ * b, hgamma⟩
    simpa using h.symm)

/-- Descending the original section does not change any chosen representative. -/
@[simp] theorem observationQuotientSection_mk {Gamma : Subgroup G} (c : ObservationSection Gamma) (g : G) :
    observationQuotientSection c (QuotientGroup.mk g) = c.representative g := rfl

/-- The descended original section is an everywhere right inverse of the quotient map. -/
theorem observationQuotientSection_rightInverse {Gamma : Subgroup G} (c : ObservationSection Gamma) :
    Function.RightInverse (observationQuotientSection c) (QuotientGroup.mk : G → G ⧸ Gamma) := by
  intro x
  induction x using Quotient.inductionOn with
  | h g => exact (QuotientGroup.eq.mpr (c.correction_mem g)).symm

/-- Count all original lattice representatives over a quotient point. -/
def quotientPeriodization (Gamma : Subgroup G) (s : G ⧸ Gamma → G)
    (f : G → ℝ≥0∞) (x : G ⧸ Gamma) : ℝ≥0∞ := ∑' gamma : Gamma, f (s x * gamma)

/-- The exact left action changes the original fiber enumeration by a lattice permutation. -/
theorem quotient_periodization_translate (Gamma : Subgroup G) (s : G ⧸ Gamma → G)
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ Gamma))
    (f : G → ℝ≥0∞) (a : G) (x : G ⧸ Gamma) :
    quotientPeriodization Gamma s (fun g => f (a * g)) x = quotientPeriodization Gamma s f (a • x) := by
  have he : (QuotientGroup.mk (s (a • x)) : G ⧸ Gamma) = QuotientGroup.mk (a * s x) := by
    rw [hs]
    change a • x = a • (QuotientGroup.mk (s x) : G ⧸ Gamma)
    rw [hs]
  let delta : Gamma := ⟨(s (a • x))⁻¹ * (a * s x), QuotientGroup.eq.mp he⟩
  have hdelta : s (a • x) * delta = a * s x := by simp [delta]
  unfold quotientPeriodization
  calc
    (∑' gamma : Gamma, f (a * (s x * gamma))) =
        ∑' gamma : Gamma, f (s (a • x) * (delta * gamma : Gamma)) := by
      congr 1
      funext gamma
      simp only [Subgroup.coe_mul, ← mul_assoc, hdelta]
    _ = _ := (Equiv.mulLeft delta).tsum_eq (fun gamma : Gamma => f (s (a • x) * gamma))

/-- The strict domain fixed by a quotient section. -/
def quotientSectionDomain (Gamma : Subgroup G) (s : G ⧸ Gamma → G) : Set G :=
  {g | s (QuotientGroup.mk g) = g}

/-- The chosen point is the only original lattice translate lying in the strict section domain. -/
theorem quotient_section_domain_translate (Gamma : Subgroup G) (s : G ⧸ Gamma → G)
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ Gamma))
    (x : G ⧸ Gamma) (gamma : Gamma) :
    s x * gamma ∈ quotientSectionDomain Gamma s ↔ gamma = 1 := by
  change s (QuotientGroup.mk (s x * gamma)) = s x * gamma ↔ gamma = 1
  rw [QuotientGroup.mk_mul_of_mem (s x) gamma.property, hs]
  constructor
  · intro h
    apply Subtype.ext
    apply mul_left_cancel (a := s x)
    simpa only [Subgroup.coe_one, mul_one] using h.symm
  · rintro rfl
    simp

section Measurable
variable [MeasurableSpace G]

/-- Counting-fiber lift of the original quotient measure. -/
def quotientCountingLift (Gamma : Subgroup G) (s : G ⧸ Gamma → G) (mu : Measure (G ⧸ Gamma)) : Measure G :=
  Measure.sum (fun gamma : Gamma => mu.map (fun x => s x * gamma))

/-- A measurable original section remains measurable after descent. -/
theorem observationQuotientSection_measurable {Gamma : Subgroup G} (c : ObservationSection Gamma)
    (hc : Measurable c.representative) : Measurable (observationQuotientSection c) :=
  QuotientGroup.measurable_from_quotient.mpr hc

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [PolishSpace G]

omit [IsTopologicalGroup G] in
/-- A fixed section's strict domain is Borel. -/
theorem quotient_section_domain_measurable (Gamma : Subgroup G) (s : G ⧸ Gamma → G)
    (hs : Measurable s) : MeasurableSet (quotientSectionDomain Gamma s) :=
  measurableSet_eq_fun (hs.comp QuotientGroup.measurable_coe) measurable_id

omit [PolishSpace G] in
/-- Periodization over the original countable lattice is measurable. -/
theorem quotient_periodization_measurable (Gamma : Subgroup G) [Countable Gamma]
    (s : G ⧸ Gamma → G) (hs : Measurable s) (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable (quotientPeriodization Gamma s f) :=
  Measurable.tsum (fun gamma => hf.comp (hs.mul_const (gamma : G)))

omit [PolishSpace G] in
/-- The lift integrates exactly the sum over the original lattice fiber. -/
theorem quotient_countingLift_lintegral (Gamma : Subgroup G) [Countable Gamma]
    (s : G ⧸ Gamma → G) (hs : Measurable s) (mu : Measure (G ⧸ Gamma))
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂quotientCountingLift Gamma s mu) = ∫⁻ x, quotientPeriodization Gamma s f x ∂mu := by
  rw [quotientCountingLift, lintegral_sum_measure]
  simp_rw [lintegral_map hf (hs.mul_const _)]
  exact (lintegral_tsum (fun (gamma : Gamma) => (hf.comp (hs.mul_const (gamma : G))).aemeasurable)).symm

omit [PolishSpace G] in
/-- Full original-group invariance downstairs implies left Haar invariance of the counting lift. -/
theorem quotient_countingLift_leftInvariant (Gamma : Subgroup G) [Countable Gamma]
    [BorelSpace (G ⧸ Gamma)] (s : G ⧸ Gamma → G) (hs : Measurable s)
    (hright : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ Gamma))
    (mu : Measure (G ⧸ Gamma)) [SMulInvariantMeasure G (G ⧸ Gamma) mu] :
    IsMulLeftInvariant (quotientCountingLift Gamma s mu) := by
  constructor
  intro a
  apply Measure.ext_of_lintegral
  intro f hf
  have hfa : Measurable (fun g : G => f (a * g)) := hf.comp (continuous_const_mul a).measurable
  rw [lintegral_map hf (continuous_const_mul a).measurable,
    quotient_countingLift_lintegral Gamma s hs mu (fun g => f (a * g)) hfa,
    quotient_countingLift_lintegral Gamma s hs mu f hf]
  simp_rw [quotient_periodization_translate Gamma s hright f a]
  exact (measurePreserving_smul a mu).lintegral_comp (quotient_periodization_measurable Gamma s hs f hf)

/-- Restricting the lift to its strict section domain and projecting recovers the original measure. -/
theorem quotient_countingLift_recover (Gamma : Subgroup G) [Countable Gamma]
    (s : G ⧸ Gamma → G) (hs : Measurable s)
    (hright : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ Gamma))
    (mu : Measure (G ⧸ Gamma)) :
    ((quotientCountingLift Gamma s mu).restrict (quotientSectionDomain Gamma s)).map QuotientGroup.mk = mu := by
  classical
  ext A hA
  have hpre := hA.preimage (QuotientGroup.measurable_coe (G := G) (S := Gamma))
  have hD := quotient_section_domain_measurable Gamma s hs
  have hmk (x : G ⧸ Gamma) : (QuotientGroup.mk (s x) : G ⧸ Gamma) = x := hright x
  rw [Measure.map_apply QuotientGroup.measurable_coe hA, Measure.restrict_apply hpre,
    quotientCountingLift, Measure.sum_apply _ (hpre.inter hD)]
  have hterm (gamma : Gamma) :
      (fun x : G ⧸ Gamma => s x * gamma) ⁻¹'
        (QuotientGroup.mk ⁻¹' A ∩ quotientSectionDomain Gamma s) =
        if gamma = 1 then A else ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      QuotientGroup.mk_mul_of_mem (s x) gamma.property, hmk,
      quotient_section_domain_translate Gamma s hright x gamma]
    by_cases h : gamma = 1 <;> simp [h]
  simp_rw [Measure.map_apply (hs.mul_const _) (hpre.inter hD), hterm, apply_ite]
  simp only [measure_empty, tsum_ite_eq]

/-- The strict section domain has precisely the original quotient's total mass. -/
theorem quotient_countingLift_domain_mass (Gamma : Subgroup G) [Countable Gamma]
    (s : G ⧸ Gamma → G) (hs : Measurable s)
    (hright : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ Gamma))
    (mu : Measure (G ⧸ Gamma)) :
    quotientCountingLift Gamma s mu (quotientSectionDomain Gamma s) = mu Set.univ := by
  have h := congrArg (fun nu : Measure (G ⧸ Gamma) => nu Set.univ)
    (quotient_countingLift_recover Gamma s hs hright mu)
  simpa only [Measure.map_apply QuotientGroup.measurable_coe MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using h

/-- Bounded section values make the counting lift finite on every compact set.
Only finitely many original lattice translates can meet that set. -/
theorem quotient_countingLift_finite_compacts (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (s : G ⧸ Gamma → G) (hs : Measurable s) (K : Set G) (hK : IsCompact K)
    (hbound : ∀ x, s x ∈ K) (mu : Measure (G ⧸ Gamma)) [IsFiniteMeasure mu] :
    IsFiniteMeasureOnCompacts (quotientCountingLift Gamma s mu) := by
  classical
  constructor
  intro C hC
  have hclosed : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  have hfinite : (Subtype.val ⁻¹' (K⁻¹ * C) : Set Gamma).Finite :=
    (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hC)).finite_of_discrete
  let I : Finset Gamma := hfinite.toFinset
  rw [quotientCountingLift, Measure.sum_apply _ hC.measurableSet]
  rw [tsum_eq_sum (s := I) (fun gamma hgamma => ?_)]
  · exact ENNReal.sum_lt_top.mpr (fun gamma _ => measure_lt_top _ _)
  · rw [Measure.map_apply (hs.mul_const _) hC.measurableSet]
    have hempty : (fun x : G ⧸ Gamma => s x * gamma) ⁻¹' C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hgamma
      change gamma ∈ hfinite.toFinset
      apply hfinite.mem_toFinset.mpr
      exact ⟨(s x)⁻¹, by simpa using hbound x, s x * gamma, hx, by simp⟩
    rw [hempty, measure_empty]

end Measurable
end GMZP0
