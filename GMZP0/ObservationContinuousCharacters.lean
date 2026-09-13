import GMZP0.ObservationCharacters
import Mathlib.Topology.Instances.RealVectorSpace

/-! Continuous characters on the actual product space G × V have real-linear
fiber restrictions. The function space carries its pointwise subspace topology.
No joint continuity of the translation action, Lie structure or lattice
cocompactness is inferred from this topology alone. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Transport the actual product topology along the pair coordinates. -/
instance observationGroupTopology (V : ObservationModule G) :
    TopologicalSpace (ObservationGroup V) :=
  TopologicalSpace.induced (fun a : ObservationGroup V => (a.base, a.obs)) inferInstance

/-- The original base inclusion is continuous in the actual product topology. -/
theorem observation_base_inclusion_continuous (V : ObservationModule G) :
    Continuous (observationBaseInclusion V) := by
  apply continuous_induced_rng.mpr
  exact continuous_id.prodMk continuous_const

/-- The actual real observation fiber embeds continuously. -/
theorem observation_fiber_inclusion_continuous (V : ObservationModule G) :
    Continuous (fun P : V.space => observationFiberInclusion V (Multiplicative.ofAdd P)) := by
  apply continuous_induced_rng.mpr
  exact continuous_const.prodMk continuous_id

/-- Restricting a continuous character to the original base preserves continuity. -/
theorem observation_character_base_continuous (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi) :
    Continuous (observationCharacterBase V chi) :=
  hchi.comp (observation_base_inclusion_continuous V)

/-- The additive fiber restriction inherits continuity from the actual character. -/
theorem observation_character_fiber_continuous (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi) :
    Continuous (observationCharacterFiber V chi) :=
  continuous_toAdd.comp (hchi.comp (observation_fiber_inclusion_continuous V))

/-- The actual continuous fiber restriction, now proved real-linear. -/
def observationContinuousFiber (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi) : V.space →L[ℝ] ℝ :=
  (observationCharacterFiber V chi).toRealLinearMap
    (observation_character_fiber_continuous V chi hchi)

/-- The real-linear map agrees with the original character on every actual fiber element. -/
@[simp] theorem observationContinuousFiber_apply (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi) (P : V.space) :
    observationContinuousFiber V chi hchi P = observationCharacterFiber V chi P := rfl

/-- Every actual continuous character has the full real-linear form, with W annihilated. -/
theorem observation_continuous_character_form (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi) :
    observationDifferenceSpace V ≤ LinearMap.ker (observationContinuousFiber V chi hchi).toLinearMap ∧
      ∀ a : ObservationGroup V, (chi a).toAdd =
        (observationCharacterBase V chi a.base).toAdd + observationContinuousFiber V chi hchi a.obs :=
  observation_character_linear_form V chi (observationContinuousFiber V chi hchi).toLinearMap
    (fun _ => rfl)

/-- The actual continuous character loses the entire original source term on the exact curve. -/
theorem observation_continuous_character_curve (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (hW : observationConstant V h1 1 ∈ observationDifferenceSpace V)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi)
    (g : G) (F : V.space) (source A : ℝ) :
    (chi (observationCurvePoint V h1 g F source A)).toAdd =
      (observationCharacterBase V chi g).toAdd - A * observationContinuousFiber V chi hchi F :=
  observation_actual_character_curve V h1 hW chi
    (observationContinuousFiber V chi hchi).toLinearMap (fun _ => rfl) g F source A

/-- Integrality of the continuous character supplies integrality of its actual linear fiber map. -/
theorem observation_continuous_fiber_integral (V : ObservationModule G) (Gamma : Subgroup G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi)
    (hint : ∀ l : observationLatticeSubgroup V Gamma, ∃ n : ℤ, (chi l).toAdd = n)
    (P : observationIntegerFunctions V Gamma) :
    ∃ n : ℤ, observationContinuousFiber V chi hchi P = n :=
  observation_character_fiber_integral V Gamma chi hint P

/-- A nontrivial actual character gives a nontrivial pair of base and real-linear fiber parts. -/
theorem observation_continuous_character_nontrivial (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (hchi : Continuous chi) (hne : chi ≠ 1) :
    observationCharacterBase V chi ≠ 1 ∨ observationContinuousFiber V chi hchi ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  apply MonoidHom.ext
  intro a
  apply Multiplicative.toAdd.injective
  have hf := (observation_continuous_character_form V chi hchi).2 a
  simpa [h.1, h.2] using hf

end GMZP0
