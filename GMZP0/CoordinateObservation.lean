import GMZP0.WeightedSubstitution
import GMZP0.ObservationFlag
import Mathlib.LinearAlgebra.Pi

/-! A concrete common flag from actual polynomial coordinates and lower-weight
translation corrections. Polynomial representatives are witnesses, not new fields
that may replace the underlying observation functions. -/
noncomputable section
open MvPolynomial
namespace GMZP0
variable {G sigma : Type*} [Group G]

/-- Evaluate one actual coordinate polynomial at all points of G. -/
def coordinatePolynomialEvaluation (coord : G → sigma → ℝ) :
    MvPolynomial sigma ℝ →ₗ[ℝ] (G → ℝ) :=
  LinearMap.pi (fun u => (MvPolynomial.aeval (coord u)).toLinearMap)

omit [Group G] in
@[simp] theorem coordinatePolynomialEvaluation_apply (coord : G → sigma → ℝ)
    (P : MvPolynomial sigma ℝ) (u : G) :
    coordinatePolynomialEvaluation coord P u = MvPolynomial.aeval (coord u) P := rfl

/-- Coordinate substitution represents actual left translation at every group point. -/
theorem coordinate_evaluation_translate (coord : G → sigma → ℝ)
    (q : G → sigma → MvPolynomial sigma ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (g : G) (P : MvPolynomial sigma ℝ) :
    coordinatePolynomialEvaluation coord (weightedTriangularSubstitution (q g) P) =
      fun u => coordinatePolynomialEvaluation coord P (g * u) := by
  funext u
  simp only [coordinatePolynomialEvaluation_apply, weightedTriangularSubstitution,
    MvPolynomial.comp_aeval_apply, map_add, MvPolynomial.aeval_X]
  apply congrArg (fun v : sigma → ℝ => MvPolynomial.aeval v P)
  funext i
  exact (hcoord g u i).symm

/-- The flag is the intersection of V with the actual bounded polynomial-value space. -/
def coordinateObservationFlag (V : ObservationModule G) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) (n : ℕ) : Submodule ℝ V.space :=
  ((weightedPolynomialBelow w n).map (coordinatePolynomialEvaluation coord)).comap V.space.subtype

/-- Flag membership provides a polynomial representing exactly the same observation function. -/
theorem mem_coordinateObservationFlag (V : ObservationModule G) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) (n : ℕ) (F : V.space) :
    F ∈ coordinateObservationFlag V coord w n ↔
      ∃ P ∈ weightedPolynomialBelow w n, coordinatePolynomialEvaluation coord P = F.val := by
  exact Submodule.mem_map

/-- The actual zero level is bottom, even when the coordinate map is not surjective. -/
theorem coordinateObservationFlag_zero (V : ObservationModule G) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) : coordinateObservationFlag V coord w 0 = ⊥ := by
  apply le_antisymm
  · intro F hF
    obtain ⟨P, hP, he⟩ := (mem_coordinateObservationFlag V coord w 0 F).mp hF
    rw [weightedPolynomialBelow_zero] at hP
    have hp : P = 0 := hP
    change F = 0
    apply Subtype.ext
    change F.val = 0
    simpa only [hp, map_zero] using he.symm
  · exact bot_le

/-- The constructed flag is increasing. -/
theorem coordinateObservationFlag_mono (V : ObservationModule G) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) {a b : ℕ} (hab : a ≤ b) :
    coordinateObservationFlag V coord w a ≤ coordinateObservationFlag V coord w b := by
  intro F hF
  obtain ⟨P, hP, he⟩ := (mem_coordinateObservationFlag V coord w a F).mp hF
  exact (mem_coordinateObservationFlag V coord w b F).mpr
    ⟨P, weightedPolynomialBelow_mono w hab hP, he⟩

/-- The flag strictly lowers every actual translation difference in V. -/
theorem coordinateObservationFlag_lowers (V : ObservationModule G) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) (q : G → sigma → MvPolynomial sigma ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hq : ∀ g i, q g i ∈ weightedPolynomialBelow w (w i))
    (n : ℕ) (g : G) (F : V.space) (hF : F ∈ coordinateObservationFlag V coord w (n + 1)) :
    observationTranslate V g F - F ∈ coordinateObservationFlag V coord w n := by
  obtain ⟨P, hP, he⟩ := (mem_coordinateObservationFlag V coord w (n + 1) F).mp hF
  apply (mem_coordinateObservationFlag V coord w n _).mpr
  refine ⟨weightedTriangularSubstitution (q g) P - P,
    weighted_substitution_difference w (q g) (hq g) P n hP, ?_⟩
  rw [map_sub, coordinate_evaluation_translate coord q hcoord, he]
  rfl

/-- An actual uniform polynomial-value bound supplies the top level before any translations. -/
theorem coordinateObservationFlag_top (V : ObservationModule G) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) (K : ℕ)
    (hbound : V.space ≤ (weightedPolynomialBelow w K).map (coordinatePolynomialEvaluation coord)) :
    ∀ F : V.space, F ∈ coordinateObservationFlag V coord w K := by
  intro F
  exact hbound F.property

/-- Constructed coordinate flag removes the abstract flag premise from the constant-in-W step. -/
theorem observation_one_mem_difference_of_coordinates (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (coord : G → sigma → ℝ)
    (w : sigma → ℕ) (q : G → sigma → MvPolynomial sigma ℝ) (K : ℕ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hq : ∀ g i, q g i ∈ weightedPolynomialBelow w (w i))
    (hbound : V.space ≤ (weightedPolynomialBelow w K).map (coordinatePolynomialEvaluation coord))
    (hnonconstant : ∃ (P : V.space) (u : G), P u ≠ P 1) :
    observationConstant V h1 1 ∈ observationDifferenceSpace V := by
  exact observation_one_mem_difference_of_flag V h1 (coordinateObservationFlag V coord w) K
    (coordinateObservationFlag_zero V coord w) (coordinateObservationFlag_top V coord w K hbound)
    (coordinateObservationFlag_lowers V coord w q hcoord hq) hnonconstant

end GMZP0
