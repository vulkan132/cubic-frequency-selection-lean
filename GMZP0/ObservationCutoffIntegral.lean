import GMZP0.ObservationFiberIntegral
import GMZP0.ObservationFiberGeometry

/-! The original observation's constant-translation symmetry on H/Gamma_H.
A global zero-mean theorem is conditional on an actual invariant finite
measure and measurability; neither of those global inputs is constructed here. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G]

/-- The original group element adding a real constant to every observation function. -/
def observationConstantElement (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (a : ℝ) : ObservationGroup V :=
  ⟨1, observationConstant V h1 a⟩

/-- Left translation by an actual constant element preserves the original base coset. -/
theorem observation_constant_action_base (V : ObservationModule G) (Gamma : Subgroup G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (a : ℝ)
    (x : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) :
    observationQuotientBaseProjection V Gamma (observationConstantElement V h1 a • x) =
      observationQuotientBaseProjection V Gamma x := by
  induction x using Quotient.inductionOn with
  | h z =>
    change QuotientGroup.mk (1 * z.base) = QuotientGroup.mk z.base
    rw [one_mul]

/-- The exact original quotient observation acquires the constant character under this action. -/
theorem quotient_observation_constant_action (V : ObservationModule G) {Gamma : Subgroup G}
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma) (a : ℝ)
    (x : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) :
    quotientObservation V c (observationConstantElement V h1 a • x) =
      circleCharacter (a : Frequency) * quotientObservation V c x := by
  induction x using Quotient.inductionOn with
  | h z =>
    change circleCharacter (observationRealPhase V c (observationConstantElement V h1 a * z) :
      Frequency) = circleCharacter (a : Frequency) * circleCharacter (observationRealPhase V c z : Frequency)
    have he : observationRealPhase V c (observationConstantElement V h1 a * z) =
        a + observationRealPhase V c z := by
      simp [observationRealPhase, observationConstantElement, observation_mul_obs]
    rw [he, AddCircle.coe_add, circleCharacter_add]

/-- A cutoff depending only on the original base retains the exact half-translation sign. -/
theorem quotient_observation_cutoff_half_action (V : ObservationModule G) {Gamma : Subgroup G}
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma)
    (chi : G ⧸ Gamma → ℂ) (x : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) :
    chi (observationQuotientBaseProjection V Gamma (observationConstantElement V h1 (1 / 2) • x)) *
      quotientObservation V c (observationConstantElement V h1 (1 / 2) • x) =
        -(chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) := by
  rw [observation_constant_action_base, quotient_observation_constant_action, observation_half_character]
  ring

/-- For an actual invariant finite measure, a measurable bounded base cutoff has genuine zero mean.
Construction of that global invariant measure and section measurability remain separate obligations. -/
theorem quotient_observation_cutoff_integral_zero (V : ObservationModule G) {Gamma : Subgroup G}
    [MeasurableSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]
    [MeasurableConstSMul (ObservationGroup V)
      (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma)]
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma)
    (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
    [IsFiniteMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu]
    (chi : G ⧸ Gamma → ℂ) (C : ℝ) (hC : ∀ z, ‖chi z‖ ≤ C)
    (hm : AEStronglyMeasurable
      (fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) mu) :
    Integrable (fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x) mu ∧
      (∫ x, chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x ∂mu) = 0 := by
  let f := fun x => chi (observationQuotientBaseProjection V Gamma x) * quotientObservation V c x
  have hint : Integrable f mu := by
    apply (integrable_const C).mono' hm
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul, quotient_observation_norm, mul_one]
    exact hC _
  refine ⟨hint, ?_⟩
  have he := integral_smul_eq_self (μ := mu) f (g := observationConstantElement V h1 (1 / 2))
  have hneg : (fun x => f (observationConstantElement V h1 (1 / 2) • x)) = fun x => -f x :=
    funext (quotient_observation_cutoff_half_action V h1 c chi)
  rw [hneg, integral_neg] at he
  have hzero : (2 : ℂ) * (∫ x, f x ∂mu) = 0 := by linear_combination -he
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

end GMZP0
