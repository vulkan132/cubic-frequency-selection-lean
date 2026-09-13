import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Actual weighted polynomial subspaces, indexed by a strict support bound.
Level zero is the zero subspace, including when all nonzero terms cancel. -/
noncomputable section
open scoped BigOperators Pointwise
open MvPolynomial
namespace GMZP0
variable {sigma : Type*}

/-- Every monomial with nonzero coefficient has weight strictly less than n. -/
def weightedPolynomialBelow (w : sigma → ℕ) (n : ℕ) :
    Submodule ℝ (MvPolynomial sigma ℝ) where
  carrier := {P | ∀ d ∈ P.support, Finsupp.weight w d < n}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro P Q hP hQ d hd
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact hP d h
    · exact hQ d h
  smul_mem' := by
    intro a P hP d hd
    exact hP d (MvPolynomial.support_smul hd)

/-- Membership refers to actual support, not to a selected syntactic expression. -/
theorem mem_weightedPolynomialBelow (w : sigma → ℕ) (n : ℕ) (P : MvPolynomial sigma ℝ) :
    P ∈ weightedPolynomialBelow w n ↔ ∀ d ∈ P.support, Finsupp.weight w d < n := Iff.rfl

/-- The degree-zero flag level contains only the zero polynomial. -/
theorem weightedPolynomialBelow_zero (w : sigma → ℕ) : weightedPolynomialBelow w 0 = ⊥ := by
  apply le_antisymm
  · intro P hP
    change P = 0
    apply MvPolynomial.ext
    intro d
    by_contra hd
    have hcoeff : P.coeff d ≠ 0 := by simpa using hd
    exact Nat.not_lt_zero _ (hP d (MvPolynomial.mem_support_iff.mpr hcoeff))
  · exact bot_le

/-- Increasing the declared level preserves membership. -/
theorem weightedPolynomialBelow_mono (w : sigma → ℕ) {a b : ℕ} (hab : a ≤ b) :
    weightedPolynomialBelow w a ≤ weightedPolynomialBelow w b := by
  intro P hP d hd
  exact (hP d hd).trans_le hab

/-- An actual monomial has its exact exponent-weight bound even when its coefficient is zero. -/
theorem weighted_monomial_mem (w : sigma → ℕ) (d : sigma →₀ ℕ) (a : ℝ) :
    monomial d a ∈ weightedPolynomialBelow w (Finsupp.weight w d + 1) := by
  classical
  intro e he
  have heq : e = d := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
  subst e
  exact Nat.lt_succ_self _

/-- Constants lie at level one. -/
theorem weighted_constant_mem (w : sigma → ℕ) (a : ℝ) :
    C a ∈ weightedPolynomialBelow w 1 := by
  simpa using weighted_monomial_mem w 0 a

/-- Each coordinate has the declared weight bound. -/
theorem weighted_variable_mem (w : sigma → ℕ) (i : sigma) :
    X i ∈ weightedPolynomialBelow w (w i + 1) := by
  simpa [MvPolynomial.X, Finsupp.weight_single] using
    weighted_monomial_mem w (Finsupp.single i 1) 1

/-- Product support adds the actual exponent vectors, giving the non-strict degree bound. -/
theorem weighted_mul_le (w : sigma → ℕ) {P Q : MvPolynomial sigma ℝ} {a b : ℕ}
    (hP : P ∈ weightedPolynomialBelow w (a + 1))
    (hQ : Q ∈ weightedPolynomialBelow w (b + 1)) :
    P * Q ∈ weightedPolynomialBelow w (a + b + 1) := by
  classical
  intro d hd
  obtain ⟨e, he, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp := hP e he
  have hq := hQ f hf
  rw [map_add]
  omega

/-- A strict gain in one factor survives multiplication by a bounded-degree factor. -/
theorem weighted_mul_lt (w : sigma → ℕ) {P Q : MvPolynomial sigma ℝ} {a b : ℕ}
    (hP : P ∈ weightedPolynomialBelow w a)
    (hQ : Q ∈ weightedPolynomialBelow w (b + 1)) :
    P * Q ∈ weightedPolynomialBelow w (a + b) := by
  classical
  intro d hd
  obtain ⟨e, he, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp := hP e he
  have hq := hQ f hf
  rw [map_add]
  omega

/-- The strict gain may occur in the right factor as well. -/
theorem weighted_mul_lt_right (w : sigma → ℕ) {P Q : MvPolynomial sigma ℝ} {a b : ℕ}
    (hP : P ∈ weightedPolynomialBelow w (a + 1))
    (hQ : Q ∈ weightedPolynomialBelow w b) :
    P * Q ∈ weightedPolynomialBelow w (a + b) := by
  simpa only [mul_comm Q P, Nat.add_comm b a] using weighted_mul_lt w hQ hP

/-- Substitution by coordinates with strictly lower-weight corrections. -/
def weightedTriangularSubstitution (q : sigma → MvPolynomial sigma ℝ) :
    MvPolynomial sigma ℝ →ₐ[ℝ] MvPolynomial sigma ℝ :=
  MvPolynomial.aeval (fun i => X i + q i)

/-- A product difference splits into two terms, each retaining a strict weight gain. -/
theorem weighted_substitution_product (w : sigma → ℕ) (q : sigma → MvPolynomial sigma ℝ)
    {P Q : MvPolynomial sigma ℝ} {a b : ℕ}
    (hP : P ∈ weightedPolynomialBelow w (a + 1))
    (hQ : Q ∈ weightedPolynomialBelow w (b + 1))
    (htP : weightedTriangularSubstitution q P ∈ weightedPolynomialBelow w (a + 1))
    (htQ : weightedTriangularSubstitution q Q ∈ weightedPolynomialBelow w (b + 1))
    (hdP : weightedTriangularSubstitution q P - P ∈ weightedPolynomialBelow w a)
    (hdQ : weightedTriangularSubstitution q Q - Q ∈ weightedPolynomialBelow w b) :
    P * Q ∈ weightedPolynomialBelow w (a + b + 1) ∧
      weightedTriangularSubstitution q (P * Q) ∈ weightedPolynomialBelow w (a + b + 1) ∧
      weightedTriangularSubstitution q (P * Q) - P * Q ∈ weightedPolynomialBelow w (a + b) := by
  rw [map_mul]
  refine ⟨weighted_mul_le w hP hQ, weighted_mul_le w htP htQ, ?_⟩
  have he : weightedTriangularSubstitution q P * weightedTriangularSubstitution q Q - P * Q =
      (weightedTriangularSubstitution q P - P) * weightedTriangularSubstitution q Q +
        P * (weightedTriangularSubstitution q Q - Q) := by ring
  rw [he]
  exact (weightedPolynomialBelow w (a + b)).add_mem
    (weighted_mul_lt w hdP htQ) (weighted_mul_lt_right w hP hdQ)

end GMZP0
