import GMZP0.OriginalLeftInvariantCoordinates

/-! Exact obstruction to identifying first- and second-input velocities.
The polynomial is the central coordinate x₃+y₃+x₁y₂ of Heisenberg multiplication. -/
noncomputable section
open MvPolynomial
namespace GMZP0

/-- The central multiplication polynomial in the three-dimensional example. -/
def heisenbergCentralPolynomial : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ :=
  X (Sum.inl 2) + X (Sum.inr 2) + X (Sum.inl 0) * X (Sum.inr 1)

/-- Differentiating the first variable in direction e₁ and setting that
input to the identity gives the second coordinate of the other point;
differentiating the second input in direction e₁ gives zero instead. -/
theorem heisenberg_first_second_input_obstruction :
    aeval (Sum.elim (fun _ : Fin 3 => (0 : MvPolynomial (Fin 3) ℚ)) X)
      (pderiv (Sum.inl 0) heisenbergCentralPolynomial) = X 1 ∧
    aeval (Sum.elim X (fun _ : Fin 3 => (0 : MvPolynomial (Fin 3) ℚ)))
      (pderiv (Sum.inr 0) heisenbergCentralPolynomial) = 0 ∧
    (X (1 : Fin 3) : MvPolynomial (Fin 3) ℚ) ≠ 0 := by
  constructor
  · simp [heisenbergCentralPolynomial, pderiv_X]
  constructor
  · simp [heisenbergCentralPolynomial, pderiv_X]
  · exact X_ne_zero 1

end GMZP0
