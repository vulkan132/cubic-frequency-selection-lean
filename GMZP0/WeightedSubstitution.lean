import GMZP0.WeightedPolynomial

/-! Lower coordinate corrections imply strict lowering for every polynomial.
The argument expands actual monomials and keeps cancellations in the support. -/
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace GMZP0
variable {sigma : Type*}

/-- The pair of degree bounds and strict difference bound is closed under powers. -/
theorem weighted_substitution_power (w : sigma → ℕ) (q : sigma → MvPolynomial sigma ℝ)
    (P : MvPolynomial sigma ℝ) (a n : ℕ)
    (hP : P ∈ weightedPolynomialBelow w (a + 1))
    (htP : weightedTriangularSubstitution q P ∈ weightedPolynomialBelow w (a + 1))
    (hdP : weightedTriangularSubstitution q P - P ∈ weightedPolynomialBelow w a) :
    P ^ n ∈ weightedPolynomialBelow w (n * a + 1) ∧
      weightedTriangularSubstitution q (P ^ n) ∈ weightedPolynomialBelow w (n * a + 1) ∧
      weightedTriangularSubstitution q (P ^ n) - P ^ n ∈ weightedPolynomialBelow w (n * a) := by
  induction n with
  | zero =>
    simpa using And.intro (weighted_constant_mem w 1)
      (And.intro (weighted_constant_mem w 1) ((weightedPolynomialBelow w 0).zero_mem))
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using
      weighted_substitution_product w q ih.1 hP ih.2.1 htP ih.2.2 hdP

/-- The coordinate correction hypothesis supplies the full substitution bounds for a variable. -/
theorem weighted_substitution_variable (w : sigma → ℕ) (q : sigma → MvPolynomial sigma ℝ)
    (hq : ∀ i, q i ∈ weightedPolynomialBelow w (w i)) (i : sigma) :
    X i ∈ weightedPolynomialBelow w (w i + 1) ∧
      weightedTriangularSubstitution q (X i) ∈ weightedPolynomialBelow w (w i + 1) ∧
      weightedTriangularSubstitution q (X i) - X i ∈ weightedPolynomialBelow w (w i) := by
  have he : weightedTriangularSubstitution q (X i) = X i + q i := by
    simp [weightedTriangularSubstitution]
  refine ⟨weighted_variable_mem w i, ?_, ?_⟩
  · rw [he]
    exact (weightedPolynomialBelow w (w i + 1)).add_mem (weighted_variable_mem w i)
      (weightedPolynomialBelow_mono w (Nat.le_succ _) (hq i))
  · rw [he, add_sub_cancel_left]
    exact hq i

/-- Substitution preserves a monomial's weight bound and strictly lowers its difference. -/
theorem weighted_substitution_monomial (w : sigma → ℕ) (q : sigma → MvPolynomial sigma ℝ)
    (hq : ∀ i, q i ∈ weightedPolynomialBelow w (w i)) (d : sigma →₀ ℕ) (r : ℝ) :
    monomial d r ∈ weightedPolynomialBelow w (Finsupp.weight w d + 1) ∧
      weightedTriangularSubstitution q (monomial d r) ∈
        weightedPolynomialBelow w (Finsupp.weight w d + 1) ∧
      weightedTriangularSubstitution q (monomial d r) - monomial d r ∈
        weightedPolynomialBelow w (Finsupp.weight w d) := by
  classical
  induction d using Finsupp.induction with
  | zero =>
    have he : weightedTriangularSubstitution q (C r) = C r := by
      simp [weightedTriangularSubstitution]
    simp only [map_zero, zero_add]
    change C r ∈ weightedPolynomialBelow w 1 ∧
      weightedTriangularSubstitution q (C r) ∈ weightedPolynomialBelow w 1 ∧
      weightedTriangularSubstitution q (C r) - C r ∈ weightedPolynomialBelow w 0
    rw [he, sub_self]
    exact ⟨weighted_constant_mem w r, weighted_constant_mem w r,
      (weightedPolynomialBelow w 0).zero_mem⟩
  | @single_add i n d hi hn ih =>
    have hv := weighted_substitution_variable w q hq i
    have hp := weighted_substitution_power w q (X i) (w i) n hv.1 hv.2.1 hv.2.2
    have hprod := weighted_substitution_product w q ih.1 hp.1 ih.2.1 hp.2.1 ih.2.2 hp.2.2
    simpa only [add_comm (Finsupp.single i n) d, monomial_add_single, map_add,
      Finsupp.weight_single, nsmul_eq_mul, Nat.cast_id] using hprod

/-- Strict lowering of the difference at every declared degree, including the zero level. -/
theorem weighted_substitution_difference (w : sigma → ℕ) (q : sigma → MvPolynomial sigma ℝ)
    (hq : ∀ i, q i ∈ weightedPolynomialBelow w (w i))
    (P : MvPolynomial sigma ℝ) (n : ℕ) (hP : P ∈ weightedPolynomialBelow w (n + 1)) :
    weightedTriangularSubstitution q P - P ∈ weightedPolynomialBelow w n := by
  classical
  have he : weightedTriangularSubstitution q P - P =
      ∑ d ∈ P.support,
        (weightedTriangularSubstitution q (monomial d (P.coeff d)) - monomial d (P.coeff d)) := by
    rw [Finset.sum_sub_distrib, ← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [he]
  apply Submodule.sum_mem
  intro d hd
  exact weightedPolynomialBelow_mono w (by have hh := hP d hd; omega)
    (weighted_substitution_monomial w q hq d (P.coeff d)).2.2

/-- The actual substitution preserves every weighted degree bound. -/
theorem weighted_substitution_preserves (w : sigma → ℕ) (q : sigma → MvPolynomial sigma ℝ)
    (hq : ∀ i, q i ∈ weightedPolynomialBelow w (w i))
    (P : MvPolynomial sigma ℝ) (n : ℕ) (hP : P ∈ weightedPolynomialBelow w n) :
    weightedTriangularSubstitution q P ∈ weightedPolynomialBelow w n := by
  have hd := weighted_substitution_difference w q hq P n
    (weightedPolynomialBelow_mono w (Nat.le_succ _) hP)
  simpa only [sub_add_cancel] using (weightedPolynomialBelow w n).add_mem hd hP

end GMZP0
