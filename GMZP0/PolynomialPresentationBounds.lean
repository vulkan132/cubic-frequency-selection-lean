import GMZP0.RationalObservationTranslation
import GMZP0.ObservationNilpotent
import Mathlib.Algebra.MvPolynomial.Funext

/-! Uniform degree bounds from the fixed original polynomial presentation.
The bounds precede every translating point and every unrestricted real
observation. No bounded-coefficient or separately supplied degree premise
is used. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0

/-- Substitution of polynomials of degree at most D multiplies the actual
total degree by at most D, including zero polynomials and empty supports. -/
theorem polynomial_substitution_totalDegree_le {sigma tau : Type*}
    (v : sigma → MvPolynomial tau ℝ) (D : ℕ)
    (hv : ∀ i, (v i).totalDegree ≤ D) (p : MvPolynomial sigma ℝ) :
    (MvPolynomial.aeval v p).totalDegree ≤ p.totalDegree * D := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  change (C (p.coeff d) * ∏ i ∈ d.support, v i ^ d i).totalDegree ≤ _
  calc
    _ ≤ (C (p.coeff d) : MvPolynomial tau ℝ).totalDegree +
        (∏ i ∈ d.support, v i ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ d.support, v i ^ d i).totalDegree := by rw [totalDegree_C, zero_add]
    _ ≤ ∑ i ∈ d.support, (v i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i * D := Finset.sum_le_sum fun i _ =>
      (MvPolynomial.totalDegree_pow (v i) (d i)).trans (Nat.mul_le_mul_left (d i) (hv i))
    _ = (d.sum fun _ e => e) * D := by simp only [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * D := Nat.mul_le_mul_right D (MvPolynomial.le_totalDegree hd)

/-- Fixing the first vector in the literal joint law gives exactly its
original second-coordinate polynomial evaluation. -/
theorem polynomial_partial_joint_eval {sigma : Type*}
    (p : MvPolynomial (sigma ⊕ sigma) ℝ) (x y : sigma → ℝ) :
    MvPolynomial.aeval y
      (MvPolynomial.aeval (Sum.elim (fun i => C (x i)) X) p) =
      MvPolynomial.aeval (Sum.elim x y) p := by
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : (sigma ⊕ sigma) → ℝ => MvPolynomial.aeval v p)
  funext i
  cases i <;> simp

/-- A fixed joint law internally bounds every original triangular
correction, uniformly over all translating group elements. Surjective
original coordinates identify the actual polynomials, not just a finite
set of their values. -/
theorem original_triangular_correction_uniform_degree
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i =
      MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i)) :
    ∃ D : ℕ, ∀ g i, (q g i).totalDegree ≤ D := by
  classical
  let r := fun i => (p i).map (algebraMap ℚ ℝ)
  refine ⟨max 1 (Finset.univ.sup fun i => (r i).totalDegree), ?_⟩
  intro g i
  have heq : q g i =
      MvPolynomial.aeval (Sum.elim (fun j => C (coord g j)) X) (r i) +
        (-1 : ℝ) • X i := by
    apply MvPolynomial.funext
    intro x
    obtain ⟨u, rfl⟩ := coord.surjective x
    change MvPolynomial.aeval (coord u) (q g i) = _
    change _ = MvPolynomial.aeval (coord u) (_ + _)
    rw [map_add, map_smul, polynomial_partial_joint_eval, MvPolynomial.aeval_X]
    have hj : MvPolynomial.aeval (Sum.elim (coord g) (coord u)) (r i) = coord (g * u) i := by
      change MvPolynomial.eval (Sum.elim (coord g) (coord u)) ((p i).map (algebraMap ℚ ℝ)) = _
      rw [MvPolynomial.eval_map]
      exact (hjoint g u i).symm
    rw [hj, htri]
    simp
  rw [heq]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · have hv : ∀ j : Fin m ⊕ Fin m,
        ((Sum.elim (fun k => C (coord g k)) X) j : MvPolynomial (Fin m) ℝ).totalDegree ≤ 1 := by
      intro j
      cases j <;> simp
    have hdeg := polynomial_substitution_totalDegree_le _ 1 hv (r i)
    have hdeg' : (MvPolynomial.aeval (Sum.elim (fun j => C (coord g j)) X) (r i)).totalDegree ≤
        (r i).totalDegree := by simpa using hdeg
    exact hdeg'.trans
      ((Finset.le_sup (f := fun i => (r i).totalDegree) (Finset.mem_univ i)).trans (le_max_right _ _))
  · exact (MvPolynomial.totalDegree_smul_le (-1 : ℝ) (X i)).trans
      (by simp)

/-- One degree bound chosen from the fixed basis represents every actual
observation, with no bound on its real coefficients. -/
theorem observation_rational_basis_uniform_degree
    {G sigma iota : Type*} [Group G] [Fintype iota]
    (V : ObservationModule G) (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    ∃ R : ℕ, ∀ F : V.space, ∃ Q : MvPolynomial sigma ℝ,
      Q.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord Q = F.val := by
  classical
  let r := fun i => (P i).map (algebraMap ℚ ℝ)
  refine ⟨Finset.univ.sup (fun i => (r i).totalDegree), ?_⟩
  intro F
  refine ⟨∑ i, b.repr F i • r i, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    exact (MvPolynomial.totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun i => (r i).totalDegree) hi)
  · have hbi (i : iota) : coordinatePolynomialEvaluation coord (r i) = (b i).val := by
      funext g
      change MvPolynomial.eval (coord g) ((P i).map (algebraMap ℚ ℝ)) = b i g
      rw [MvPolynomial.eval_map]
      exact (hP i g).symm
    rw [map_sum]
    simp_rw [map_smul, hbi]
    have he := congrArg V.space.subtype (b.sum_repr F)
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using he

end GMZP0
