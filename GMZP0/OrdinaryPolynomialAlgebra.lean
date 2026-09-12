import GMZP0.ConstantFreezing
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree

/-! Bounded-degree polynomial substitutions and the exact ordinary double-phase polynomial. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace GMZP0

/-- Affine substitution does not increase degree, including zero slope and the zero polynomial. -/
theorem ordinary_affine_comp_degree (P : ℝ[X]) (D : ℕ) (hP : P.natDegree ≤ D) (s t : ℝ) :
    (P.comp (C s * X + C t)).natDegree ≤ D := by
  have hq : (C s * X + C t : ℝ[X]).natDegree ≤ 1 := by compute_degree
  exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul hP hq)

/-- The degree-D coefficient transforms by s^D even when the actual degree is smaller than D. -/
theorem ordinary_affine_comp_coeff (P : ℝ[X]) (D : ℕ) (hP : P.natDegree ≤ D) (s t : ℝ) :
    (P.comp (C s * X + C t)).coeff D = P.coeff D * s ^ D := by
  have hq : (C s * X + C t : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hpow : ((C s * X + C t : ℝ[X]) ^ D).coeff D = s ^ D := by
    simpa only [Nat.mul_one, coeff_add, coeff_C_mul_X, if_true, coeff_C,
      show (1 : ℕ) ≠ 0 by decide, if_false, add_zero] using
      (coeff_pow_of_natDegree_le (m := D) hq)
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)]
  simp only [sum_comp, C_mul_comp, X_pow_comp, finsetSum_coeff, coeff_C_mul]
  rw [Finset.sum_eq_single D]
  · rw [hpow]
  · intro i hi hne
    have hiD : i < D := by have hi' := Finset.mem_range.mp hi; omega
    have hdeg : ((C s * X + C t : ℝ[X]) ^ i).natDegree < D :=
      (natDegree_pow_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left i hq)).trans_lt hiD
    rw [coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self D))).elim

def cubicShiftDifference (h k : ℝ) : ℝ[X] :=
  (X + C (k - h)) ^ 3 - (X - C h) ^ 3

/-- Exact cancellation of the cubic term in the original two shifted labels. -/
theorem cubicShiftDifference_expansion (h k : ℝ) :
    cubicShiftDifference h k =
      C (3 * k) * X ^ 2 + C (3 * k ^ 2 - 6 * k * h) * X + C ((k - h) ^ 3 + h ^ 3) := by
  simp only [cubicShiftDifference, map_sub, map_add, map_pow, map_mul, map_ofNat]
  ring

theorem cubicShiftDifference_degree (h k : ℝ) : (cubicShiftDifference h k).natDegree ≤ 2 := by
  rw [cubicShiftDifference_expansion]
  compute_degree

theorem cubicShiftDifference_coeff_two (h k : ℝ) : (cubicShiftDifference h k).coeff 2 = 3 * k := by
  rw [cubicShiftDifference_expansion]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

def ordinaryDoublePhasePolynomial (A B : ℝ[X]) (y h k : ℝ) : ℝ[X] :=
  C (A.eval y) * (X + C k) ^ 3 - C (A.eval (y + 2 * h * k)) * X ^ 3 -
    B.comp (C (2 * h) * X + C (y + 2 * h * k - h ^ 2)) * cubicShiftDifference h k

/-- This polynomial evaluates to the full double phase, before any coefficient or norm estimate. -/
theorem ordinaryDoublePhasePolynomial_eval (A B : ℝ[X]) (y h k r : ℝ) :
    (ordinaryDoublePhasePolynomial A B y h k).eval r =
      (r + k) ^ 3 * A.eval y - r ^ 3 * A.eval (y + 2 * h * k) -
        ((r + k - h) ^ 3 - (r - h) ^ 3) * B.eval (y + 2 * h * (r + k) - h ^ 2) := by
  simp only [ordinaryDoublePhasePolynomial, cubicShiftDifference, eval_sub, eval_mul,
    eval_C, eval_pow, eval_add, eval_X, eval_comp]
  have he : 2 * h * r + (y + 2 * h * k - h ^ 2) = y + 2 * h * (r + k) - h ^ 2 := by ring
  rw [he]
  ring

/-- The complete phase has degree at most D+2 for D>=1; no top coefficient is assumed nonzero. -/
theorem ordinaryDoublePhasePolynomial_degree (A B : ℝ[X]) (D : ℕ) (hD : 1 ≤ D)
    (hB : B.natDegree ≤ D) (y h k : ℝ) :
    (ordinaryDoublePhasePolynomial A B y h k).natDegree ≤ D + 2 := by
  have hfirst : (C (A.eval y) * (X + C k) ^ 3 - C (A.eval (y + 2 * h * k)) * X ^ 3).natDegree ≤ 3 := by
    compute_degree
  have hsecond : (B.comp (C (2 * h) * X + C (y + 2 * h * k - h ^ 2)) *
      cubicShiftDifference h k).natDegree ≤ D + 2 :=
    natDegree_mul_le.trans (Nat.add_le_add (ordinary_affine_comp_degree B D hB _ _)
      (cubicShiftDifference_degree h k))
  have hfirst' : (C (A.eval y) * (X + C k) ^ 3 - C (A.eval (y + 2 * h * k)) * X ^ 3).natDegree ≤ D + 2 :=
    hfirst.trans (by omega)
  simpa only [ordinaryDoublePhasePolynomial, max_self] using natDegree_sub_le_of_le hfirst' hsecond

/-- The true degree-(D+2) coefficient is root-independent, with all integer factors retained. -/
theorem ordinaryDoublePhasePolynomial_top_coeff (A B : ℝ[X]) (D : ℕ) (hD : 2 ≤ D)
    (hB : B.natDegree ≤ D) (y h k : ℝ) :
    (ordinaryDoublePhasePolynomial A B y h k).coeff (D + 2) =
      -3 * k * (2 * h) ^ D * B.coeff D := by
  have hfirst : (C (A.eval y) * (X + C k) ^ 3 - C (A.eval (y + 2 * h * k)) * X ^ 3).natDegree ≤ 3 := by
    compute_degree
  have hzero : (C (A.eval y) * (X + C k) ^ 3 - C (A.eval (y + 2 * h * k)) * X ^ 3).coeff (D + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hfirst.trans_lt (by omega))
  rw [ordinaryDoublePhasePolynomial, coeff_sub, hzero,
    coeff_mul_add_eq_of_natDegree_le (ordinary_affine_comp_degree B D hB _ _)
      (cubicShiftDifference_degree h k), ordinary_affine_comp_coeff B D hB,
    cubicShiftDifference_coeff_two]
  ring

/-- D=1 is a real exception: the first two phase terms can contribute a nonzero cubic coefficient. -/
theorem ordinary_degree_one_top_obstruction :
    (ordinaryDoublePhasePolynomial (X : ℝ[X]) 0 0 1 1).coeff 3 = -2 := by
  norm_num [ordinaryDoublePhasePolynomial, coeff_sub, coeff_C_mul]

theorem ordinary_eval_degree_zero (P : ℝ[X]) (hP : P.natDegree ≤ 0) (y : ℝ) :
    P.eval y = P.coeff 0 := by
  conv_lhs => rw [eq_C_of_natDegree_le_zero hP]
  rw [eval_C]

theorem ordinary_eval_degree_one (P : ℝ[X]) (hP : P.natDegree ≤ 1) (y : ℝ) :
    P.eval y = y * P.coeff 1 + P.coeff 0 := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (show P.natDegree < 2 by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, eval_add, eval_mul, eval_C, eval_X]
  ring

end GMZP0
