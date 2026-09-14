import GMZP0.CoordinateObservation
import GMZP0.ObservationContinuousCharacters
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Finite-dimensionality comes from the actual polynomial representatives.
It is not included as an unproved field in the observation module. -/
noncomputable section
open Module
namespace GMZP0
variable {G sigma : Type*} [Group G] [Finite sigma]

/-- The actual function space obtained by evaluating bounded-degree polynomials. -/
def coordinatePolynomialSpace (coord : G → sigma → ℝ) (R : ℕ) : Submodule ℝ (G → ℝ) :=
  (MvPolynomial.restrictTotalDegree sigma ℝ R).map (coordinatePolynomialEvaluation coord)

omit [Group G] in
/-- Bounded-degree polynomial values form a finite-dimensional space, even with redundant coordinates. -/
theorem coordinatePolynomialSpace_finiteDimensional (coord : G → sigma → ℝ) (R : ℕ) :
    FiniteDimensional ℝ (coordinatePolynomialSpace coord R) := by
  unfold coordinatePolynomialSpace
  infer_instance

omit [Finite sigma] in
/-- Actual polynomial representatives place V in the bounded polynomial-value space. -/
theorem observation_le_coordinatePolynomialSpace (V : ObservationModule G)
    (coord : G → sigma → ℝ) (R : ℕ)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    V.space ≤ coordinatePolynomialSpace coord R := by
  intro F hF
  obtain ⟨P, hdeg, he⟩ := hP ⟨F, hF⟩
  exact Submodule.mem_map.mpr ⟨P, (MvPolynomial.mem_restrictTotalDegree sigma R P).mpr hdeg, he⟩

/-- A uniform ordinary degree bound proves finite-dimensionality of the original observation space. -/
theorem observation_finiteDimensional_of_degree (V : ObservationModule G)
    (coord : G → sigma → ℝ) (R : ℕ)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    FiniteDimensional ℝ V.space := by
  let : FiniteDimensional ℝ (coordinatePolynomialSpace coord R) :=
    coordinatePolynomialSpace_finiteDimensional coord R
  exact Submodule.finiteDimensional_of_le (observation_le_coordinatePolynomialSpace V coord R hP)

/-- The dimension bound depends on the fixed polynomial space, before any actual coefficients. -/
theorem observation_finrank_le_polynomial (V : ObservationModule G)
    (coord : G → sigma → ℝ) (R : ℕ)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    Module.finrank ℝ V.space ≤ Module.finrank ℝ (MvPolynomial.restrictTotalDegree sigma ℝ R) := by
  let : FiniteDimensional ℝ (coordinatePolynomialSpace coord R) :=
    coordinatePolynomialSpace_finiteDimensional coord R
  exact (Submodule.finrank_mono (observation_le_coordinatePolynomialSpace V coord R hP)).trans
    (Submodule.finrank_map_le (coordinatePolynomialEvaluation coord) _)

/-- The pointwise subspace topology is the finite-dimensional real module topology. -/
theorem observation_has_moduleTopology (V : ObservationModule G) [FiniteDimensional ℝ V.space] :
    IsModuleTopology ℝ V.space := isModuleTopologyOfFiniteDimensional

/-- Every actual fixed translation is continuous in the observation space's pointwise topology. -/
theorem observation_translate_continuous (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (g : G) : Continuous (observationTranslate V g) :=
  (observationTranslate V g).continuous_of_finiteDimensional

/-- The actual difference space W is closed; no replacement by a topological closure is needed. -/
theorem observation_difference_closed (V : ObservationModule G) [FiniteDimensional ℝ V.space] :
    IsClosed (observationDifferenceSpace V : Set V.space) :=
  (observationDifferenceSpace V).closed_of_finiteDimensional

/-- Any finite real basis identifies the pointwise topology with the usual real coordinate topology. -/
theorem observation_basis_coordinates_continuous (V : ObservationModule G)
    {iota : Type*} [Finite iota] (b : Basis iota ℝ V.space) : Continuous b.equivFun :=
  continuous_equivFun_basis b

end GMZP0
