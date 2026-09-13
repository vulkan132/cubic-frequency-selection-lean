import GMZP0.ObservationQuotient
import GMZP0.WideLagBounds

/-! The actual observation-group curve for the original complete block phase.
The curve is encoded exactly. Polynomial degrees, rational presentations and
equidistribution are deliberately separate from this identity. -/
noncomputable section
open scoped BigOperators
namespace GMZP0
variable {G : Type*} [Group G]

/-- The curve point (g, source*1 - A*(F composed with L_g)). -/
def observationCurvePoint (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (g : G) (F : V.space)
    (source A : ℝ) : ObservationGroup V :=
  ⟨g, observationConstant V h1 source - A • observationTranslate V g F⟩

/-- Evaluation of this curve yields the exact desired phase at the canonical representative. -/
theorem observation_curve_real_phase (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (g : G) (F : V.space) (source A : ℝ) :
    observationRealPhase V c (observationCurvePoint V h1 g F source A) =
      source - A * F (c.representative g) := by
  change source - A * F (g * observationCorrection c g) = _
  rw [observation_representative_eq]

/-- The same exact phase is obtained from the quotient observation. -/
theorem observation_curve_quotient (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (g : G) (F : V.space) (source A : ℝ) :
    quotientObservation V c (Quotient.mk _ (observationCurvePoint V h1 g F source A)) =
      circleCharacter ((source - A * F (c.representative g) : ℝ) : Frequency) := by
  rw [quotient_observation_mk, observation_curve_real_phase]

/-- Values of one supplied observation family, on all integer vertical coordinates. -/
def observationVerticalValue (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (x : Fin N) (y : ℤ) : ℝ :=
  F x y (c.representative (g x y))

/-- The same values viewed on the circle, with no changes of roots. -/
def observationVerticalProfile (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (x : Fin N) (y : ℤ) : Frequency :=
  (observationVerticalValue V c g F x y : Frequency)

/-- The original finite-box field obtained by restriction of the same observation. -/
def observationOriginalProfile (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (z : Base N) : Frequency :=
  observationVerticalProfile V c g F z.1 (label z.2)

/-- There is exact full-profile agreement at every original base point. -/
theorem observation_profile_agreement (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) : WideProfileAgreement N
      (observationVerticalProfile V c g F) (observationOriginalProfile V c g F) := by
  intro x y
  rfl

/-- The finite operator retains the original function and every original response label. -/
theorem observation_profile_original_response (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (f : ℤ × ℤ → ℂ) (z : Base N) :
    finiteResponse N (observationOriginalProfile V c g F) (fun u => f (inputPoint u)) z =
      response N f z (observationOriginalProfile V c g F z) :=
  finiteResponse_original N (observationOriginalProfile V c g F) f z

/-- The observation-group point at each actual original block label and original root. -/
def observationBlockCurve (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (x x' : Fin N) (y k r : ℤ) : ObservationGroup V :=
  let h := horizontalGap x x'
  let Y := y + 2 * h * (r + k) - h ^ 2
  observationCurvePoint V h1 (g x' Y) (F x' Y)
    (((r + k : ℤ) : ℝ) ^ 3 * observationVerticalValue V c g F x y -
      (r : ℝ) ^ 3 * observationVerticalValue V c g F x (y + 2 * h * k))
    (((r + k - h : ℤ) : ℝ) ^ 3 - ((r - h : ℤ) : ℝ) ^ 3)

/-- The curve phase equals the actual complete double phase, at every integer label. -/
theorem observation_block_circle_phase (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (x x' : Fin N) (y k r : ℤ) :
    (observationRealPhase V c (observationBlockCurve V h1 c g F x x' y k r) : Frequency) =
      wideDoublePhase (observationVerticalProfile V c g F) x x' y k r := by
  unfold observationBlockCurve
  rw [observation_curve_real_phase]
  simp only [wideDoublePhase, doublePhaseCoefficient, observationVerticalProfile,
    observationVerticalValue, ← AddCircle.coe_zsmul, ← AddCircle.coe_sub,
    zsmul_eq_mul, Int.cast_sub, Int.cast_pow]

/-- The full actual lag sum is the fixed quotient observation of this curve.
The roots, intersection of label intervals and all multiplicities are unchanged. -/
theorem observation_wide_lag_sum (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) {N : ℕ} (g : Fin N → ℤ → G)
    (F : Fin N → ℤ → V.space) (x x' : Fin N) (y k : ℤ) :
    wideLagSum (observationVerticalProfile V c g F) x x' y k =
      ∑ r ∈ lagLabels N (horizontalGap x x') k,
        quotientObservation V c (Quotient.mk _ (observationBlockCurve V h1 c g F x x' y k r)) := by
  apply Finset.sum_congr rfl
  intro r _
  rw [quotient_observation_mk, observation_block_circle_phase]

/-- An invariant fiber functional combines with a base character to give a group character. -/
def observationHorizontalCharacter (V : ObservationModule G)
    (eta : G →* Multiplicative ℝ) (ell : V.space →ₗ[ℝ] ℝ)
    (hell : observationDifferenceSpace V ≤ LinearMap.ker ell) :
    ObservationGroup V →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd ((eta a.base).toAdd + ell a.obs)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change (eta 1).toAdd + ell 0 = 0
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change (eta (a.base * b.base)).toAdd +
      ell (observationTranslate V b.base a.obs + b.obs) =
        ((eta a.base).toAdd + ell a.obs) + ((eta b.base).toAdd + ell b.obs)
    rw [map_mul, toAdd_mul, map_add,
      (observation_annihilator_iff V ell).mp hell]
    abel

/-- If one lies in the actual difference space, the complete source polynomial vanishes
in the horizontal character, with no assumption on its size or degree. -/
theorem observation_character_curve (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (hW : observationConstant V h1 1 ∈ observationDifferenceSpace V)
    (eta : G →* Multiplicative ℝ) (ell : V.space →ₗ[ℝ] ℝ)
    (hell : observationDifferenceSpace V ≤ LinearMap.ker ell)
    (g : G) (F : V.space) (source A : ℝ) :
    (observationHorizontalCharacter V eta ell hell
      (observationCurvePoint V h1 g F source A)).toAdd =
        (eta g).toAdd - A * ell F := by
  have hc : ell (observationConstant V h1 source) = 0 :=
    hell (observation_constant_mem_difference V h1 hW source)
  change (eta g).toAdd + ell (observationConstant V h1 source -
    A • observationTranslate V g F) = _
  rw [map_sub, map_smul, hc, (observation_annihilator_iff V ell).mp hell]
  simp [sub_eq_add_neg]

end GMZP0
