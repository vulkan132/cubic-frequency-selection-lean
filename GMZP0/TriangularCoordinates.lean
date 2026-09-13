import GMZP0.ObservationProper
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Explicit weights and flags for triangular coordinate presentations.
Weights depend only on the coordinate degree bound and dimension, never on
the real coefficients or on the translating group element. -/
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace GMZP0
variable {sigma G : Type*}

/-- Monomial weight is bounded by its actual total degree times the largest variable weight. -/
theorem weighted_monomial_weight_le (w : sigma → ℕ) (d : sigma →₀ ℕ) (B : ℕ)
    (hB : ∀ i ∈ d.support, w i ≤ B) :
    Finsupp.weight w d ≤ (d.sum (fun _ e => e)) * B := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => Nat.mul_le_mul_left (d i) (hB i hi))

/-- An ordinary coordinate-degree bound gives a uniform weighted level. -/
theorem weighted_polynomial_mem_of_totalDegree (w : sigma → ℕ) (B R : ℕ)
    (hB : ∀ i, w i ≤ B) (P : MvPolynomial sigma ℝ) (hP : P.totalDegree ≤ R) :
    P ∈ weightedPolynomialBelow w (R * B + 1) := by
  intro d hd
  have hw := weighted_monomial_weight_le w d B (fun i _ => hB i)
  have hdeg := (MvPolynomial.le_totalDegree hd).trans hP
  exact lt_of_le_of_lt (hw.trans (Nat.mul_le_mul_right B hdeg)) (Nat.lt_succ_self _)

/-- Uniform weights dominating every lower-coordinate polynomial of degree at most D. -/
def triangularCoordinateWeight (D : ℕ) {m : ℕ} (i : Fin m) : ℕ := (D + 1) ^ i.val

/-- Every monomial using only earlier coordinates and of degree at most D has lower weight. -/
theorem triangular_monomial_weight_lt (D : ℕ) {m : ℕ} (i : ℕ) (d : Fin m →₀ ℕ)
    (hdeg : d.sum (fun _ e => e) ≤ D) (hlow : ∀ j ∈ d.support, j.val < i) :
    Finsupp.weight (triangularCoordinateWeight D) d < (D + 1) ^ i := by
  classical
  cases i with
  | zero =>
    have hd : d = 0 := by
      ext j
      by_contra h
      have hj : d j ≠ 0 := by simpa using h
      exact Nat.not_lt_zero _ (hlow j (Finsupp.mem_support_iff.mpr hj))
    simp [hd]
  | succ i =>
    have hB : ∀ j ∈ d.support, triangularCoordinateWeight D j ≤ (D + 1) ^ i := by
      intro j hj
      exact pow_le_pow_right₀ (by omega : 1 ≤ D + 1) (by have hh := hlow j hj; omega)
    have hw := (weighted_monomial_weight_le (triangularCoordinateWeight D) d
      ((D + 1) ^ i) hB).trans (Nat.mul_le_mul_right _ hdeg)
    have hlt : D * (D + 1) ^ i < (D + 1) * (D + 1) ^ i :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self D) (pow_pos (by omega) i)
    simpa only [pow_succ, Nat.mul_comm (D + 1) ((D + 1) ^ i)] using hw.trans_lt hlt

/-- Each actual triangular coordinate correction satisfies the needed strict weighted bound. -/
theorem triangular_correction_mem (D : ℕ) {m : ℕ} (i : Fin m)
    (P : MvPolynomial (Fin m) ℝ) (hdeg : P.totalDegree ≤ D)
    (hlow : ∀ d ∈ P.support, ∀ j ∈ d.support, j.val < i.val) :
    P ∈ weightedPolynomialBelow (triangularCoordinateWeight D) (triangularCoordinateWeight D i) := by
  intro d hd
  exact triangular_monomial_weight_lt D i.val d ((MvPolynomial.le_totalDegree hd).trans hdeg)
    (hlow d hd)

variable [Group G]

/-- Ordinary bounded-degree representatives put the actual observation module in a fixed flag level. -/
theorem triangular_observation_uniform_bound (V : ObservationModule G) {m : ℕ}
    (coord : G → Fin m → ℝ) (D R : ℕ)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial (Fin m) ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    V.space ≤ (weightedPolynomialBelow (triangularCoordinateWeight D)
      (R * (D + 1) ^ m + 1)).map (coordinatePolynomialEvaluation coord) := by
  intro F hF
  obtain ⟨P, hdeg, he⟩ := hP ⟨F, hF⟩
  apply Submodule.mem_map.mpr
  refine ⟨P, ?_, he⟩
  apply weighted_polynomial_mem_of_totalDegree _ _ R _ P hdeg
  intro i
  exact pow_le_pow_right₀ (by omega : 1 ≤ D + 1) i.isLt.le

/-- Actual triangular coordinate formulas construct the common flag and prove 1 in W, W proper.
The explicit flag height depends only on D, R and the number of coordinates. -/
theorem observation_difference_structure_of_triangular (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) {m : ℕ}
    (coord : G → Fin m → ℝ) (q : G → Fin m → MvPolynomial (Fin m) ℝ) (D R : ℕ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hqdeg : ∀ g i, (q g i).totalDegree ≤ D)
    (hqlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial (Fin m) ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val)
    (hnonconstant : ∃ (P : V.space) (u : G), P u ≠ P 1) :
    observationConstant V h1 1 ∈ observationDifferenceSpace V ∧ observationDifferenceSpace V ≠ ⊤ := by
  apply observation_difference_structure_of_coordinates V h1 coord (triangularCoordinateWeight D) q
    (R * (D + 1) ^ m + 1) hcoord _ (triangular_observation_uniform_bound V coord D R hP) hnonconstant
  intro g i
  exact triangular_correction_mem D i (q g i) (hqdeg g i) (hqlow g i)

end GMZP0
