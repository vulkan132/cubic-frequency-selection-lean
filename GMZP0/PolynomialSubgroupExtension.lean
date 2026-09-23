import GMZP0.PolynomialNaturalIdentity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat

/-! A polynomial-coordinate curve agreeing with every natural power
of an original element inherits the full real subgroup law. All
extensions use identities on the entire natural grid. -/
noncomputable section
namespace GMZP0

/-- Evaluation in real time commutes with substitution into each
original rational polynomial. -/
theorem rational_polynomial_substitution_eval {sigma : Type*}
    (P : MvPolynomial sigma ℚ) (a : sigma → Polynomial ℝ) (t : ℝ) :
    (MvPolynomial.aeval a P).eval t = MvPolynomial.aeval (fun j => (a j).eval t) P := by
  let ev : Polynomial ℝ →ₐ[ℚ] ℝ := Polynomial.aevalTower (AlgHom.id ℚ ℝ) t
  exact MvPolynomial.comp_aeval_apply a ev P

/-- Exact original natural powers determine a polynomial-coordinate
curve's group law for every pair of real parameters. -/
theorem polynomial_curve_subgroup_of_nat_powers
    {G sigma : Type*} [Group G] (coord : G → sigma → ℝ) (hinj : Function.Injective coord)
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (gamma : ℝ → G) (g : G) (P : sigma → Polynomial ℝ)
    (hP : ∀ t i, coord (gamma t) i = (P i).eval t)
    (hnat : ∀ n : ℕ, gamma (n : ℝ) = g ^ n) :
    ∀ s t, gamma (s + t) = gamma s * gamma t := by
  have hleft (n : ℕ) (t : ℝ) (i : sigma) :
      coord (gamma ((n : ℝ) + t)) i = coord (gamma (n : ℝ) * gamma t) i := by
    let A := (P i).comp (Polynomial.C (n : ℝ) + Polynomial.X)
    let B : Polynomial ℝ := MvPolynomial.aeval
      (Sum.elim (fun j => Polynomial.C (coord (gamma (n : ℝ)) j)) P) (p i)
    have hA (s : ℝ) : A.eval s = coord (gamma ((n : ℝ) + s)) i := by
      simp [A, hP, Polynomial.eval_comp]
    have hB (s : ℝ) : B.eval s = coord (gamma (n : ℝ) * gamma s) i := by
      rw [show B = MvPolynomial.aeval
        (Sum.elim (fun j => Polynomial.C (coord (gamma (n : ℝ)) j)) P) (p i) from rfl,
        rational_polynomial_substitution_eval, hjoint]
      apply congrArg (fun x : sigma ⊕ sigma → ℝ => MvPolynomial.aeval x (p i))
      funext j
      cases j <;> simp [hP]
    have he : A = B := by
      apply polynomial_eq_of_nat_evaluations
      intro k
      rw [hA, hB, ← Nat.cast_add, hnat, hnat, hnat, pow_add]
    rw [← hA t, ← hB t, he]
  intro s t
  apply hinj
  funext i
  let A := (P i).comp (Polynomial.X + Polynomial.C t)
  let B : Polynomial ℝ := MvPolynomial.aeval
    (Sum.elim P (fun j => Polynomial.C (coord (gamma t) j))) (p i)
  have hA (u : ℝ) : A.eval u = coord (gamma (u + t)) i := by
    simp [A, hP, Polynomial.eval_comp]
  have hB (u : ℝ) : B.eval u = coord (gamma u * gamma t) i := by
    rw [show B = MvPolynomial.aeval
      (Sum.elim P (fun j => Polynomial.C (coord (gamma t) j))) (p i) from rfl,
      rational_polynomial_substitution_eval, hjoint]
    apply congrArg (fun x : sigma ⊕ sigma → ℝ => MvPolynomial.aeval x (p i))
    funext j
    cases j <;> simp [hP]
  have he : A = B := by
    apply polynomial_eq_of_nat_evaluations
    intro n
    rw [hA, hB]
    exact hleft n t i
  rw [← hA s, ← hB s, he]

end GMZP0
