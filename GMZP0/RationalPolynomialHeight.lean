import GMZP0.RationalHeightFinite
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Fixed rational coordinate arrays have one degree and reduced-height
bound for all their coefficients, including coefficients off the support. -/
noncomputable section
namespace GMZP0
variable {sigma iota : Type*}

/-- Coefficient-height bound that also includes the zero coefficient. -/
def rationalPolynomialHeight (P : MvPolynomial sigma ℚ) : ℕ :=
  max 1 (P.support.sup fun d => rationalHeight (P.coeff d))

/-- Every coefficient is bounded, without restricting to nonzero support. -/
theorem rational_polynomial_height_bound (P : MvPolynomial sigma ℚ) (d : sigma →₀ ℕ) :
    rationalHeight (P.coeff d) ≤ rationalPolynomialHeight P := by
  classical
  by_cases hd : d ∈ P.support
  · exact (Finset.le_sup (f := fun d => rationalHeight (P.coeff d)) hd).trans (le_max_right _ _)
  · have hz : P.coeff d = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using hd
    rw [hz]
    change rationalHeight 0 ≤ max 1 (P.support.sup fun d => rationalHeight (P.coeff d))
    have h0 : rationalHeight (0 : ℚ) = 1 := by norm_num [rationalHeight]
    rw [h0]
    exact le_max_left _ _

/-- One explicit number bounds degrees and coefficients of an array. -/
def rationalPolynomialArrayBound [Fintype iota] (P : iota → MvPolynomial sigma ℚ) : ℕ :=
  max 1 (max (Finset.univ.sup fun i => (P i).totalDegree)
    (Finset.univ.sup fun i => rationalPolynomialHeight (P i)))

/-- The array bound is positive and simultaneously controls every actual
total degree and every reduced coefficient height. -/
theorem rational_polynomial_array_bounds [Fintype iota]
    (P : iota → MvPolynomial sigma ℚ) :
    0 < rationalPolynomialArrayBound P ∧
      ∀ i, (P i).totalDegree ≤ rationalPolynomialArrayBound P ∧
        ∀ d, rationalHeight ((P i).coeff d) ≤ rationalPolynomialArrayBound P := by
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro i
  constructor
  · exact (Finset.le_sup (f := fun i => (P i).totalDegree) (Finset.mem_univ i)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro d
    exact (rational_polynomial_height_bound (P i) d).trans
      ((Finset.le_sup (f := fun i => rationalPolynomialHeight (P i)) (Finset.mem_univ i)).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

end GMZP0
