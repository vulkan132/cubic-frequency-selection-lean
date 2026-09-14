import GMZP0.ObservationRationalSpan
import Mathlib.Algebra.Algebra.Rat

/-! A literal rational multivariate-polynomial matrix for actual translations
supplies the finite coefficient presentation used to prove W rational. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype iota]

/-- One finite support for every entry of the fixed rational translation-difference matrix. -/
def rationalMatrixSupport (A : iota → iota → MvPolynomial sigma ℚ) : Finset (sigma →₀ ℕ) := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (A i j).support

/-- Each genuine matrix monomial occurs in the fixed combined support. -/
theorem rationalMatrixSupport_contains (A : iota → iota → MvPolynomial sigma ℚ) (i j : iota) :
    (A i j).support ⊆ rationalMatrixSupport A := by
  classical
  intro d hd
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hd⟩⟩

omit [Group G] [Fintype iota] in
/-- Rational polynomial evaluation expands over any fixed support containing its actual monomials. -/
theorem rational_polynomial_eval_on_support (P : MvPolynomial sigma ℚ)
    (S : Finset (sigma →₀ ℕ)) (hS : P.support ⊆ S) (x : sigma → ℝ) :
    MvPolynomial.aeval x P = ∑ d ∈ S, ((P.coeff d : ℚ) : ℝ) * d.prod (fun i n => x i ^ n) := by
  classical
  have hp : P = ∑ d ∈ S, MvPolynomial.monomial d (P.coeff d) := by
    calc
      P = ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d) := P.as_sum
      _ = _ := Finset.sum_subset hS (by
        intro d _ hd
        simp [MvPolynomial.notMem_support_iff.mp hd])
  calc
    MvPolynomial.aeval x P = MvPolynomial.aeval x (∑ d ∈ S, MvPolynomial.monomial d (P.coeff d)) :=
      congrArg (MvPolynomial.aeval x) hp
    _ = _ := by simp only [map_sum, MvPolynomial.aeval_monomial]; rfl

/-- In a real basis, rational polynomial matrix evaluation equals its vector coefficient expansion. -/
theorem rational_matrix_vector_expansion (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (A : iota → iota → MvPolynomial sigma ℚ) (x : sigma → ℝ) (j : iota) :
    (∑ i, MvPolynomial.aeval x (A i j) • b i) =
      vectorPolynomialValue (rationalMatrixSupport A)
        (fun d => rationalBasisVector b (fun i => (A i j).coeff d)) x := by
  classical
  simp_rw [rational_polynomial_eval_on_support _ _ (rationalMatrixSupport_contains A _ _) x]
  simp only [vectorPolynomialValue, rationalBasisVector, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- The actual coordinate entries of translation differences give the whole vector identity. -/
theorem observation_matrix_translation_expansion (V : ObservationModule G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (A : iota → iota → MvPolynomial sigma ℚ)
    (hA : ∀ g j i, b.repr (observationTranslate V g (b j) - b j) i =
      MvPolynomial.aeval (coord g) (A i j)) (g : G) (j : iota) :
    observationTranslate V g (b j) - b j =
      vectorPolynomialValue (rationalMatrixSupport A)
        (fun d => rationalBasisVector b (fun i => (A i j).coeff d)) (coord g) := by
  rw [← rational_matrix_vector_expansion]
  have he := b.sum_repr (observationTranslate V g (b j) - b j)
  simpa only [hA] using he.symm

/-- A genuine rational polynomial translation matrix proves rationality of the actual W. -/
theorem observation_difference_rational_of_matrix (V : ObservationModule G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ) (hcoord : Function.Surjective coord)
    (A : iota → iota → MvPolynomial sigma ℚ)
    (hA : ∀ g j i, b.repr (observationTranslate V g (b j) - b j) i =
      MvPolynomial.aeval (coord g) (A i j)) :
    RationalInBasis b (observationDifferenceSpace V) :=
  observation_difference_rational_of_polynomial V b coord hcoord (rationalMatrixSupport A)
    (fun j d i => (A i j).coeff d) (observation_matrix_translation_expansion V b coord A hA)

end GMZP0
