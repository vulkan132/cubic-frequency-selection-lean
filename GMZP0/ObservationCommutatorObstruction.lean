import GMZP0.ObservationCommutator
import GMZP0.ObservationObstruction

/-! The additive base does not make the observation group abelian:
the actual translation action produces a nonzero central fiber commutator. -/
noncomputable section
open scoped commutatorElement
namespace GMZP0

/-- A genuine affine coordinate gives the constant-one translation difference. -/
theorem affine_observation_unit_difference :
    observationTranslate affineRealObservationModule (Multiplicative.ofAdd (1 : ℝ))
      affineRealCoordinate - affineRealCoordinate =
        observationConstant affineRealObservationModule affine_real_observation_one 1 := by
  apply Subtype.ext
  funext u
  change ((Multiplicative.ofAdd (1 : ℝ)) * u).toAdd - u.toAdd = 1
  simp

/-- In an abelian base, the base-fiber commutator can still be the nonzero constant-one fiber. -/
theorem observation_abelian_base_obstruction :
    let V := affineRealObservationModule
    let a := observationBaseInclusion V (Multiplicative.ofAdd (1 : ℝ))⁻¹
    let b := observationFiberInclusion V (Multiplicative.ofAdd affineRealCoordinate)
    ⁅a, b⁆ = observationFiberInclusion V
      (Multiplicative.ofAdd (observationConstant V affine_real_observation_one 1)) ∧ ⁅a, b⁆ ≠ 1 := by
  dsimp only
  rw [observation_commutator_base_fiber, affine_observation_unit_difference]
  refine ⟨rfl, ?_⟩
  intro h
  have he := congrArg (fun a : ObservationGroup affineRealObservationModule => a.obs 1) h
  change (1 : ℝ) = 0 at he
  exact one_ne_zero he

end GMZP0
