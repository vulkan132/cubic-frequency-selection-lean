import GMZP0.ObservationCommutator
import GMZP0.ObservationPhase
import Mathlib.GroupTheory.Abelianization.Defs

/-! Actual character restrictions and their annihilation of W.
The fiber restriction is initially additive. Real linearity, continuity and
quantitative integer-basis bounds are not inferred from a group hom alone. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- Restriction of an actual character to the original base group. -/
def observationCharacterBase (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) : G →* Multiplicative ℝ :=
  chi.comp (observationBaseInclusion V)

/-- Restriction to the actual real observation fiber, as an additive map. -/
def observationCharacterFiber (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) : V.space →+ ℝ where
  toFun P := (chi (observationFiberInclusion V (Multiplicative.ofAdd P))).toAdd
  map_zero' := by simp
  map_add' P Q := by simp only [ofAdd_add, map_mul, toAdd_mul]

/-- Every actual character decomposes into its base and additive fiber restrictions. -/
theorem observation_character_decomposition (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (a : ObservationGroup V) :
    (chi a).toAdd = (observationCharacterBase V chi a.base).toAdd +
      observationCharacterFiber V chi a.obs := by
  change (chi a).toAdd = (chi (observationBaseInclusion V a.base)).toAdd +
    (chi (observationFiberInclusion V (Multiplicative.ofAdd a.obs))).toAdd
  rw [← toAdd_mul, ← map_mul, observation_base_fiber_decomposition]

/-- The actual fiber restriction annihilates the entire real difference space. -/
theorem observation_character_annihilates_difference (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (P : V.space)
    (hP : P ∈ observationDifferenceSpace V) : observationCharacterFiber V chi P = 0 := by
  have hker := Abelianization.commutator_subset_ker chi (observation_difference_fiber_mem V P hP)
  have he : chi (observationFiberInclusion V (Multiplicative.ofAdd P)) = 1 := hker
  change (chi (observationFiberInclusion V (Multiplicative.ofAdd P))).toAdd = 0
  rw [he]
  rfl

/-- Consequently, every actual fiber character has the same value on every left translate. -/
theorem observation_character_translate_invariant (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (g : G) (P : V.space) :
    observationCharacterFiber V chi (observationTranslate V g P) = observationCharacterFiber V chi P := by
  have h := observation_character_annihilates_difference V chi _ (observation_difference_mem V g P)
  simpa only [map_sub, sub_eq_zero] using h

/-- If the actual fiber restriction has a real-linear representative, it gives the paper's full form. -/
theorem observation_character_linear_form (V : ObservationModule G)
    (chi : ObservationGroup V →* Multiplicative ℝ) (ell : V.space →ₗ[ℝ] ℝ)
    (hell : ∀ P, observationCharacterFiber V chi P = ell P) :
    observationDifferenceSpace V ≤ LinearMap.ker ell ∧
      ∀ a : ObservationGroup V, (chi a).toAdd =
        (observationCharacterBase V chi a.base).toAdd + ell a.obs := by
  constructor
  · intro P hP
    change ell P = 0
    rw [← hell]
    exact observation_character_annihilates_difference V chi P hP
  · intro a
    rw [observation_character_decomposition, hell]

/-- With real linearity supplied and 1 in W, every actual character kills the complete source term. -/
theorem observation_actual_character_curve (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (hW : observationConstant V h1 1 ∈ observationDifferenceSpace V)
    (chi : ObservationGroup V →* Multiplicative ℝ) (ell : V.space →ₗ[ℝ] ℝ)
    (hell : ∀ P, observationCharacterFiber V chi P = ell P)
    (g : G) (F : V.space) (source A : ℝ) :
    (chi (observationCurvePoint V h1 g F source A)).toAdd =
      (observationCharacterBase V chi g).toAdd - A * ell F := by
  obtain ⟨hkill, hform⟩ := observation_character_linear_form V chi ell hell
  rw [hform]
  change (observationCharacterBase V chi g).toAdd +
    ell (observationConstant V h1 source - A • observationTranslate V g F) = _
  have hc : ell (observationConstant V h1 source) = 0 :=
    hkill (observation_constant_mem_difference V h1 hW source)
  rw [map_sub, map_smul, hc, (observation_annihilator_iff V ell).mp hkill]
  simp [sub_eq_add_neg]

/-- Integrality on the actual observation lattice restricts to integrality on the original lattice. -/
theorem observation_character_base_integral (V : ObservationModule G) (Gamma : Subgroup G)
    (chi : ObservationGroup V →* Multiplicative ℝ)
    (hchi : ∀ l : observationLatticeSubgroup V Gamma, ∃ n : ℤ, (chi l).toAdd = n)
    (gamma : Gamma) : ∃ n : ℤ, (observationCharacterBase V chi gamma).toAdd = n := by
  have hg : observationBaseInclusion V gamma ∈ observationLatticeSubgroup V Gamma :=
    ⟨gamma.property, (observationIntegerFunctions V Gamma).zero_mem⟩
  exact hchi ⟨observationBaseInclusion V gamma, hg⟩

/-- Lattice integrality also restricts to the actual integer-valued observation fiber. -/
theorem observation_character_fiber_integral (V : ObservationModule G) (Gamma : Subgroup G)
    (chi : ObservationGroup V →* Multiplicative ℝ)
    (hchi : ∀ l : observationLatticeSubgroup V Gamma, ∃ n : ℤ, (chi l).toAdd = n)
    (P : observationIntegerFunctions V Gamma) :
    ∃ n : ℤ, observationCharacterFiber V chi P = n := by
  have hP : observationFiberInclusion V (Multiplicative.ofAdd P.val) ∈
      observationLatticeSubgroup V Gamma := ⟨Gamma.one_mem, P.property⟩
  exact hchi ⟨observationFiberInclusion V (Multiplicative.ofAdd P.val), hP⟩

end GMZP0
