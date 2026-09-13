import GMZP0.TriangularCoordinates

/-! An exact warning against replacing weighted lowering by ordinary-degree lowering.
The counterexample is a polynomial identity, not a numerical test of P0. -/
noncomputable section
open MvPolynomial
namespace GMZP0

/-- The triangular substitution X_1 -> X_1+X_0 leaves ordinary degree unchanged
in its difference, whereas the explicitly constructed weight decreases. -/
theorem triangular_ordinary_degree_obstruction :
    let q : Fin 2 → MvPolynomial (Fin 2) ℝ := fun i => if i = 1 then X 0 else 0
    let P : MvPolynomial (Fin 2) ℝ := X 1
    weightedTriangularSubstitution q P - P = X 0 ∧
      (weightedTriangularSubstitution q P - P).totalDegree = P.totalDegree ∧
      weightedTriangularSubstitution q P - P ∈
        weightedPolynomialBelow (triangularCoordinateWeight 1) 2 := by
  dsimp only
  have he : weightedTriangularSubstitution
      (fun i : Fin 2 => if i = 1 then (X 0 : MvPolynomial (Fin 2) ℝ) else 0) (X 1) - X 1 = X 0 := by
    simp [weightedTriangularSubstitution]
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    simp [MvPolynomial.totalDegree_X]
  · rw [he]
    simpa [triangularCoordinateWeight] using
      weighted_variable_mem (triangularCoordinateWeight 1) (0 : Fin 2)

end GMZP0
