import GMZP0.ObservationPhase
import GMZP0.CircleRoots

/-! An exact obstruction to dropping the pullback in the observation-group curve.
This concerns an algebraic shortcut, not P0. -/
noncomputable section
namespace GMZP0

/-- Genuine affine real polynomials on the additive real group, written multiplicatively. -/
def affineRealObservationModule : ObservationModule (Multiplicative ℝ) where
  space :=
    { carrier := {P | ∃ a b : ℝ, ∀ u, P u = a * u.toAdd + b}
      zero_mem' := ⟨0, 0, by intro u; simp⟩
      add_mem' := by
        rintro P Q ⟨a, b, hP⟩ ⟨c, d, hQ⟩
        refine ⟨a + c, b + d, ?_⟩
        intro u
        change P u + Q u = _
        rw [hP, hQ]
        ring
      smul_mem' := by
        rintro t P ⟨a, b, hP⟩
        refine ⟨t * a, t * b, ?_⟩
        intro u
        change t * P u = _
        rw [hP]
        ring }
  translate_mem := by
    rintro g P ⟨a, b, hP⟩
    refine ⟨a, a * g.toAdd + b, ?_⟩
    intro u
    change P (g * u) = _
    rw [hP, toAdd_mul]
    ring

/-- The ordinary coordinate polynomial t, as an actual member of the affine module. -/
def affineRealCoordinate : affineRealObservationModule.space :=
  ⟨fun u => u.toAdd, ⟨1, 0, by intro u; simp⟩⟩

/-- The constant-one membership used by the actual curve constructor. -/
theorem affine_real_observation_one :
    (fun _ : Multiplicative ℝ => (1 : ℝ)) ∈ affineRealObservationModule.space :=
  ⟨0, 1, by intro u; simp⟩

/-- For the identity coset quotient no representative correction is needed. -/
def trivialObservationSection (G : Type*) [Group G] : ObservationSection (⊥ : Subgroup G) where
  representative := id
  right_invariant := by
    intro g gamma
    have hg : (gamma : G) = 1 := gamma.property
    simp [hg]
  correction_mem := by intro g; simp

/-- The correct affine observation and the curve omitting pullback differ by half a circle.
Both use the same g, the same coordinate polynomial, and the same section. -/
theorem observation_missing_pullback_obstruction :
    let V := affineRealObservationModule
    let c := trivialObservationSection (Multiplicative ℝ)
    let g := Multiplicative.ofAdd (1 / 2 : ℝ)
    let correct := observationCurvePoint V affine_real_observation_one g affineRealCoordinate 0 1
    let naive : ObservationGroup V := ⟨g, -affineRealCoordinate⟩
    observationRealPhase V c correct = -(1 / 2 : ℝ) ∧
      observationRealPhase V c naive = 0 ∧
      ‖(observationRealPhase V c correct : Frequency) -
        (observationRealPhase V c naive : Frequency)‖ = 1 / 2 := by
  dsimp only
  have hc : observationRealPhase affineRealObservationModule
      (trivialObservationSection (Multiplicative ℝ))
      (observationCurvePoint affineRealObservationModule affine_real_observation_one
        (Multiplicative.ofAdd (1 / 2 : ℝ)) affineRealCoordinate 0 1) = -(1 / 2 : ℝ) := by
    rw [observation_curve_real_phase]
    norm_num [affineRealCoordinate, trivialObservationSection]
  have hn : observationRealPhase affineRealObservationModule
      (trivialObservationSection (Multiplicative ℝ))
      (⟨Multiplicative.ofAdd (1 / 2 : ℝ), -affineRealCoordinate⟩ :
        ObservationGroup affineRealObservationModule) = 0 := by
    simp [observationRealPhase, observationCorrection, trivialObservationSection,
      affineRealCoordinate]
  refine ⟨hc, hn, ?_⟩
  rw [hc, hn]
  simpa using zero_branch_division_counterexample.2

end GMZP0
