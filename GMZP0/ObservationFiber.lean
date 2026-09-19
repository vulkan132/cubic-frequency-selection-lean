import GMZP0.ObservationQuotient
import GMZP0.ObservationCompactCell

/-! The actual additive observation fiber, its evaluation characters and its
embedding in H/Gamma_H. No canonical-section regularity is presumed. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- The original fiber quotient, not a separately chosen coordinate torus. -/
abbrev ObservationFiber (V : ObservationModule G) (Gamma : Subgroup G) :=
  V.space ⧸ observationIntegerFunctions V Gamma

/-- Evaluation at an actual Gamma point descends to an additive circle character. -/
def observationFiberPhase (V : ObservationModule G) (Gamma : Subgroup G) (gamma : Gamma) :
    ObservationFiber V Gamma →+ Frequency :=
  QuotientAddGroup.lift (observationIntegerFunctions V Gamma)
    { toFun := fun F => (F gamma : Frequency)
      map_zero' := by simp
      map_add' := by intro F Q; change ((F gamma + Q gamma : ℝ) : Frequency) = _; simp }
    (by
      intro F hF
      obtain ⟨n, hn⟩ := hF gamma
      change (F gamma : Frequency) = 0
      rw [hn]
      simp)

/-- The phase at an original representative is its original evaluated value modulo one. -/
@[simp] theorem observationFiberPhase_mk (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) (F : V.space) :
    observationFiberPhase V Gamma gamma (QuotientAddGroup.mk F) = (F gamma : Frequency) := rfl

/-- The complex observation on the actual fiber, evaluated at an original subgroup point. -/
def observationFiberCharacter (V : ObservationModule G) (Gamma : Subgroup G) (gamma : Gamma)
    (x : ObservationFiber V Gamma) : ℂ :=
  circleCharacter (observationFiberPhase V Gamma gamma x)

/-- Every original representative gives the paper's exponential without a chosen real lift. -/
@[simp] theorem observationFiberCharacter_mk (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) (F : V.space) :
    observationFiberCharacter V Gamma gamma (QuotientAddGroup.mk F) =
      circleCharacter (F gamma : Frequency) := rfl

/-- Addition in the actual fiber multiplies the observations. -/
theorem observationFiberCharacter_add (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) (x y : ObservationFiber V Gamma) :
    observationFiberCharacter V Gamma gamma (x + y) =
      observationFiberCharacter V Gamma gamma x * observationFiberCharacter V Gamma gamma y := by
  simp only [observationFiberCharacter, map_add, circleCharacter_add]

/-- The actual fiber character has modulus one everywhere. -/
theorem observationFiberCharacter_norm (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) (x : ObservationFiber V Gamma) :
    ‖observationFiberCharacter V Gamma gamma x‖ = 1 := Circle.norm_coe _

/-- The phase is continuous in the original quotient topology. -/
theorem observationFiberPhase_continuous (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) : Continuous (observationFiberPhase V Gamma gamma) := by
  apply (QuotientAddGroup.isQuotientMap_mk (observationIntegerFunctions V Gamma)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp ((continuous_apply (gamma : G)).comp continuous_subtype_val)

/-- The actual fiber character is continuous, including across fiber coordinate faces. -/
theorem observationFiberCharacter_continuous (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) : Continuous (observationFiberCharacter V Gamma gamma) :=
  continuous_subtype_val.comp
    (AddCircle.continuous_toCircle.comp (observationFiberPhase_continuous V Gamma gamma))

/-- Half a real period has exactly the complex value -1. -/
theorem observation_half_character : circleCharacter ((1 / 2 : ℝ) : Frequency) = -1 := by
  rw [circleCharacter_real]
  have he : (((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I) =
      (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.exp_pi_mul_I]

/-- Translation by the original constant-one-half function negates the character. -/
theorem observationFiberCharacter_half_translate (V : ObservationModule G) (Gamma : Subgroup G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (gamma : Gamma) (x : ObservationFiber V Gamma) :
    observationFiberCharacter V Gamma gamma
      (QuotientAddGroup.mk (observationConstant V h1 (1 / 2)) + x) =
        -observationFiberCharacter V Gamma gamma x := by
  rw [observationFiberCharacter_add, observationFiberCharacter_mk]
  change circleCharacter ((1 / 2 : ℝ) : Frequency) * _ = _
  rw [observation_half_character, neg_one_mul]

/-- Constants make the original circle-valued evaluation surjective, not merely nonzero. -/
theorem observationFiberPhase_surjective (V : ObservationModule G) (Gamma : Subgroup G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (gamma : Gamma) :
    Function.Surjective (observationFiberPhase V Gamma gamma) := by
  intro a
  induction a using QuotientAddGroup.induction_on with
  | H a => exact ⟨QuotientAddGroup.mk (observationConstant V h1 a), rfl⟩

/-- The original half-constant class witnesses nontriviality of each fiber observation. -/
theorem observationFiberCharacter_nontrivial (V : ObservationModule G) (Gamma : Subgroup G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (gamma : Gamma) :
    ∃ x : ObservationFiber V Gamma, observationFiberCharacter V Gamma gamma x ≠ 1 := by
  refine ⟨QuotientAddGroup.mk (observationConstant V h1 (1 / 2)), ?_⟩
  rw [observationFiberCharacter_mk]
  change circleCharacter ((1 / 2 : ℝ) : Frequency) ≠ 1
  rw [observation_half_character]
  norm_num

/-- The original fiber at a fixed base representative maps to H/Gamma_H. -/
def observationFiberPoint (V : ObservationModule G) (Gamma : Subgroup G) (g : G) :
    ObservationFiber V Gamma → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma :=
  Quotient.lift (fun F => QuotientGroup.mk (⟨g, F⟩ : ObservationGroup V)) (by
    intro F Q h
    have hFQ : -F + Q ∈ observationIntegerFunctions V Gamma :=
      QuotientAddGroup.leftRel_apply.mp h
    apply QuotientGroup.eq.mpr
    refine ⟨by simp, ?_⟩
    have he : ((⟨g, F⟩ : ObservationGroup V)⁻¹ * ⟨g, Q⟩).obs = -F + Q := by
      apply Subtype.ext
      funext u
      simp
    rw [he]
    exact hFQ)

/-- The fiber parametrization uses the original pair (g,F). -/
@[simp] theorem observationFiberPoint_mk (V : ObservationModule G) (Gamma : Subgroup G)
    (g : G) (F : V.space) :
    observationFiberPoint V Gamma g (QuotientAddGroup.mk F) =
      QuotientGroup.mk (⟨g, F⟩ : ObservationGroup V) := rfl

/-- At any base representative, the original quotient observation is the actual fiber character.
The evaluation point is the section's original correction, including at boundary representatives. -/
theorem quotient_observation_fiber (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (g : G) (x : ObservationFiber V Gamma) :
    quotientObservation V c (observationFiberPoint V Gamma g x) =
      observationFiberCharacter V Gamma (observationCorrection c g) x := by
  induction x using Quotient.inductionOn with
  | h F => rfl

end GMZP0
