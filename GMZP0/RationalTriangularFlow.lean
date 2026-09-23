import GMZP0.PolynomialTimePrimitive
import GMZP0.TriangularDifferentialUniqueness
import Mathlib.Algebra.MvPolynomial.Eval

/-! A single fixed array of polynomials in time, with rational polynomial
coefficients in the full tangent, solves every strictly triangular
polynomial differential equation with its original initial coordinates. -/
noncomputable section
namespace GMZP0

/-- Simultaneously specialize the tangent variables and real time. -/
def rationalTimeEvaluation {m : ℕ} (v : Fin m → ℝ) (t : ℝ) :
    Polynomial (MvPolynomial (Fin m) ℚ) →ₐ[ℚ] ℝ :=
  Polynomial.aevalTower (MvPolynomial.aeval v) t

/-- Solve successive coordinates by exact polynomial integration.
The rational array is selected before any real tangent or time. -/
def rationalTriangularFlowPolynomial {m : ℕ}
    (R : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (i : Fin m) : Polynomial (MvPolynomial (Fin m) ℚ) :=
  Polynomial.C (MvPolynomial.C (c i)) + polynomialTimePrimitive
    (MvPolynomial.aeval (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j))
      (fun j => if _h : j.val < i.val then rationalTriangularFlowPolynomial R c j else 0)) (R i))
termination_by i.val

/-- The actual real coordinate path of the fixed rational array. -/
def rationalTriangularFlow {m : ℕ}
    (R : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v : Fin m → ℝ) (t : ℝ) (i : Fin m) : ℝ :=
  rationalTimeEvaluation v t (rationalTriangularFlowPolynomial R c i)

/-- Simultaneous specialization commutes with substitution into each
fixed rational polynomial. -/
theorem rational_time_substitution {m : ℕ}
    (P : MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (a : Fin m → Polynomial (MvPolynomial (Fin m) ℚ)) (v : Fin m → ℝ) (t : ℝ) :
    rationalTimeEvaluation v t
      (MvPolynomial.aeval (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j)) a) P) =
      MvPolynomial.aeval (Sum.elim v (fun j => rationalTimeEvaluation v t (a j))) P := by
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun z : Fin m ⊕ Fin m → ℝ => MvPolynomial.aeval z P)
  funext j
  cases j <;> simp [rationalTimeEvaluation]

/-- The entire actual initial vector is preserved, without shifting
the original identity coordinate to zero. -/
theorem rational_triangular_flow_zero {m : ℕ}
    (R : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v : Fin m → ℝ) : rationalTriangularFlow R c v 0 = fun i => (c i : ℝ) := by
  funext i
  rw [rationalTriangularFlow, rationalTriangularFlowPolynomial, map_add]
  have hz (P : Polynomial (MvPolynomial (Fin m) ℚ)) :
      rationalTimeEvaluation v 0 (polynomialTimePrimitive P) = 0 := by
    convert! polynomial_time_primitive_eval_zero
      (MvPolynomial.aeval v : MvPolynomial (Fin m) ℚ →ₐ[ℚ] ℝ).toRingHom P using 1
  rw [hz, add_zero]
  simp [rationalTimeEvaluation]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed polynomial array solves the full triangular equation at
every real time and for every unrestricted real tangent. -/
theorem rational_triangular_flow_hasDerivAt {m : ℕ}
    (R : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (hprefix : ∀ (v : Fin m → ℝ) i x y, (∀ j, j.val < i.val → x j = y j) →
      MvPolynomial.aeval (Sum.elim v x) (R i) = MvPolynomial.aeval (Sum.elim v y) (R i))
    (v : Fin m → ℝ) (t : ℝ) (i : Fin m) :
    HasDerivAt (fun s => rationalTriangularFlow R c v s i)
      (MvPolynomial.aeval (Sum.elim v (rationalTriangularFlow R c v t)) (R i)) t := by
  let a : Fin m → Polynomial (MvPolynomial (Fin m) ℚ) := fun j =>
    if _h : j.val < i.val then rationalTriangularFlowPolynomial R c j else 0
  let P := MvPolynomial.aeval
    (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j)) a) (R i)
  have hd := (polynomial_time_primitive_hasDerivAt
    (MvPolynomial.aeval v).toRingHom P t).const_add (c i : ℝ)
  convert! hd using 1
  · funext s
    rw [rationalTriangularFlow, rationalTriangularFlowPolynomial, map_add]
    have hc : rationalTimeEvaluation v s (Polynomial.C (MvPolynomial.C (c i))) = (c i : ℝ) := by
      simp [rationalTimeEvaluation]
    rw [hc]
    rfl
  · change _ = rationalTimeEvaluation v t P
    rw [show P = MvPolynomial.aeval
      (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j)) a) (R i) from rfl,
      rational_time_substitution]
    apply hprefix
    intro j hj
    simp only [a, dif_pos hj, rationalTriangularFlow]

/-- At time one the same array is a rational polynomial in every
tangent coordinate; this does not yet assert a logarithmic inverse. -/
theorem rational_triangular_flow_one {m : ℕ}
    (R : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v : Fin m → ℝ) (i : Fin m) :
    rationalTriangularFlow R c v 1 i =
      MvPolynomial.aeval v ((rationalTriangularFlowPolynomial R c i).eval 1) := by
  exact Polynomial.eval₂_at_one (MvPolynomial.aeval v).toRingHom

end GMZP0
