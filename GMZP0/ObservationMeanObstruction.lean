import GMZP0.ObservationFiberIntegral

/-! Exact obstruction to dropping the nonzero-evaluation hypothesis from
the zero-fiber-mean argument. This is not a counterexample to P0. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace GMZP0

/-- The zero space is an actual translation-invariant observation module. -/
def zeroObservationModule (G : Type*) [Group G] : ObservationModule G where
  space := ⊥
  translate_mem := by
    intro g F hF
    have hzero : F = 0 := hF
    change (fun u => F (g * u)) = 0
    rw [hzero]
    rfl

/-- Without constants or nonzero evaluation, an actual compact observation fiber has mean one.
The normalized Haar measure exists, so this is not a failure of integrability. -/
theorem observation_zero_module_mean_obstruction (G : Type*) [Group G] (Gamma : Subgroup G) :
    ∃ mu : Measure (ObservationFiber (zeroObservationModule G) Gamma),
      IsProbabilityMeasure mu ∧ IsAddHaarMeasure mu ∧
      Integrable (observationFiberCharacter (zeroObservationModule G) Gamma 1) mu ∧
      (∫ x, observationFiberCharacter (zeroObservationModule G) Gamma 1 x ∂mu) = 1 := by
  let V := zeroObservationModule G
  let : Subsingleton V.space := by change Subsingleton (⊥ : Submodule ℝ (G → ℝ)); infer_instance
  let : Subsingleton (ObservationFiber V Gamma) := ⟨by
    intro x y
    induction x using Quotient.inductionOn with
    | h F =>
      induction y using Quotient.inductionOn with
      | h Q => exact congrArg QuotientAddGroup.mk (Subsingleton.elim F Q)⟩
  let : CompactSpace (ObservationFiber V Gamma) := inferInstance
  refine ⟨observationFiberHaar V Gamma, inferInstance, inferInstance,
    observationFiberCharacter_integrable V Gamma 1 _, ?_⟩
  have he : observationFiberCharacter V Gamma 1 = fun _ => (1 : ℂ) := by
    funext x
    induction x using Quotient.inductionOn with
    | h F =>
      rw [observationFiberCharacter_mk]
      have hF : F = 0 := Subsingleton.elim _ _
      rw [hF]
      simp [circleCharacter]
  change (∫ x, observationFiberCharacter V Gamma 1 x ∂observationFiberHaar V Gamma) = 1
  rw [he]
  simp

end GMZP0
