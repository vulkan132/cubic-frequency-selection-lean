import GMZP0.CoordinateObservation
import Mathlib.GroupTheory.Subgroup.Saturated

/-! Properness of the actual difference space and saturation of its integer intersection.
No lattice basis, rationality or finite-index assertion is presumed. -/
noncomputable section
namespace GMZP0
variable {G sigma : Type*} [Group G]

/-- A finite common lowering flag makes the difference space proper in every nonzero module. -/
theorem observation_difference_proper_of_flag (V : ObservationModule G)
    (flag : ℕ → Submodule ℝ V.space) (K : ℕ)
    (hzero : flag 0 = ⊥) (htop : ∀ P : V.space, P ∈ flag K)
    (hdrop : ∀ (n : ℕ) (g : G) (P : V.space), P ∈ flag (n + 1) →
      observationTranslate V g P - P ∈ flag n)
    (hnonzero : ∃ P : V.space, P ≠ 0) : observationDifferenceSpace V ≠ ⊤ := by
  classical
  have hex : ∃ n : ℕ, ∀ P : V.space, P ∈ flag n := ⟨K, htop⟩
  have hn : 0 < Nat.find hex := by
    by_contra h
    obtain ⟨P, hP⟩ := hnonzero
    have he : Nat.find hex = 0 := by omega
    have hp := Nat.find_spec hex P
    rw [he, hzero] at hp
    exact hP hp
  have hW : observationDifferenceSpace V ≤ flag (Nat.find hex - 1) := by
    apply Submodule.span_le.mpr
    rintro Q ⟨g, P, rfl⟩
    apply hdrop
    simpa only [Nat.sub_add_cancel hn] using Nat.find_spec hex P
  intro hfull
  have hsmall : ∀ P : V.space, P ∈ flag (Nat.find hex - 1) := by
    intro P
    apply hW
    rw [hfull]
    trivial
  have hmin := Nat.find_min' hex hsmall
  omega

/-- Actual coordinate corrections and a uniform polynomial bound prove 1 in W and W proper. -/
theorem observation_difference_structure_of_coordinates (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) (q : G → sigma → MvPolynomial sigma ℝ) (K : ℕ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hq : ∀ g i, q g i ∈ weightedPolynomialBelow w (w i))
    (hbound : V.space ≤ (weightedPolynomialBelow w K).map (coordinatePolynomialEvaluation coord))
    (hnonconstant : ∃ (P : V.space) (u : G), P u ≠ P 1) :
    observationConstant V h1 1 ∈ observationDifferenceSpace V ∧ observationDifferenceSpace V ≠ ⊤ := by
  refine ⟨observation_one_mem_difference_of_coordinates V h1 coord w q K hcoord hq hbound
    hnonconstant, ?_⟩
  obtain ⟨P, _, hP⟩ := observation_difference_nonzero V hnonconstant
  exact observation_difference_proper_of_flag V (coordinateObservationFlag V coord w) K
    (coordinateObservationFlag_zero V coord w) (coordinateObservationFlag_top V coord w K hbound)
    (coordinateObservationFlag_lowers V coord w q hcoord hq) ⟨P, hP⟩

/-- The actual intersection W cap V_Z, viewed as a subgroup of V_Z itself. -/
def observationIntegerDifference (V : ObservationModule G) (Gamma : Subgroup G) :
    AddSubgroup (observationIntegerFunctions V Gamma) :=
  (observationDifferenceSpace V).toAddSubgroup.comap (observationIntegerFunctions V Gamma).subtype

/-- This integer intersection is saturated: a nonzero integer multiple cannot create W-membership.
The cancellation takes place in the real vector space, never on the circle. -/
theorem observation_integer_difference_saturated (V : ObservationModule G) (Gamma : Subgroup G) :
    (observationIntegerDifference V Gamma).toAddSubmonoid.NSMulSaturated := by
  intro n P hn
  by_cases h : n = 0
  · exact Or.inl h
  · right
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast h
    change P.val ∈ observationDifferenceSpace V
    apply ((observationDifferenceSpace V).smul_mem_iff hnR).mp
    change n • P.val ∈ observationDifferenceSpace V at hn
    simpa only [Nat.cast_smul_eq_nsmul] using hn

end GMZP0
