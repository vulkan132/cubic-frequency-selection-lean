import GMZP0.OrdinaryProfiles
import GMZP0.CircleGrid

/-! Actual lower-degree ordinary children, with every circle branch retained.
The top relation is an explicit premise; this file does not produce it from blocks. -/
noncomputable section
open Polynomial
namespace GMZP0

/-- The required top relation has its full vertical degree scale and a positive multiplier. -/
def OrdinaryTopRelation (D Q : ℕ) (E : ℝ) (N : ℕ) (a : Frequency) : Prop :=
  ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ (2 * D + 3)

/-- The degree-one instance agrees exactly with the established affine relation. -/
theorem ordinaryTopRelation_one (Q : ℕ) (E : ℝ) (N : ℕ) (a : Frequency) :
    OrdinaryTopRelation 1 Q E N a ↔ AffineTopRelation Q E N a := by
  rfl

/-- Erasing the indexed top coefficient is valid even when the actual degree is smaller. -/
theorem ordinary_erase_degree (D : ℕ) (hD : 0 < D) (P : ℝ[X]) (hP : P.natDegree ≤ D) :
    (P.erase D).natDegree ≤ D - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.2
  intro i hi
  by_cases he : i = D
  · subst i
    exact P.erase_same D
  · rw [P.erase_ne he]
    exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega))

/-- The removed monomial is the exact difference, at every real vertical argument. -/
theorem ordinary_erase_eval (D : ℕ) (P : ℝ[X]) (y : ℝ) :
    P.eval y - (P.erase D).eval y = P.coeff D * y ^ D := by
  have h := congrArg (fun R : ℝ[X] => R.eval y) (P.monomial_add_erase D)
  rw [eval_add, eval_monomial] at h
  linarith

/-- Each child is an actual real polynomial with the original lower coefficients. -/
def ordinaryChildPolynomial (D : ℕ) (P : ℝ[X]) (c : ℝ) : ℝ[X] := P.erase D + C c

/-- All nonconstant lower coefficients remain the original ones. -/
theorem ordinaryChildPolynomial_coeff (D : ℕ) (P : ℝ[X]) (c : ℝ) (i : ℕ)
    (hi : i ≠ 0) (hiD : i ≠ D) :
    (ordinaryChildPolynomial D P c).coeff i = P.coeff i := by
  simp only [ordinaryChildPolynomial, coeff_add, P.erase_ne hiD, coeff_C, if_neg hi, add_zero]

/-- The child has degree at most D-1, including a zero or lower-degree parent. -/
theorem ordinaryChildPolynomial_degree (D : ℕ) (hD : 0 < D) (P : ℝ[X])
    (hP : P.natDegree ≤ D) (c : ℝ) :
    (ordinaryChildPolynomial D P c).natDegree ≤ D - 1 := by
  apply (natDegree_add_le _ _).trans
  exact max_le (ordinary_erase_degree D hD P hP) (by simp only [natDegree_C]; omega)

/-- The child error on each original point retains the exact integer power and circle offset. -/
theorem ordinary_child_error {N : ℕ} (D : ℕ) (P : Fin N → ℝ[X]) (c : ℝ) (z : Base N) :
    ordinaryOriginalProfile P z -
      ordinaryOriginalProfile (fun x => ordinaryChildPolynomial D (P x) c) z =
        ((label z.2 : ℤ) ^ D) • ((P z.1).coeff D : Frequency) - (c : Frequency) := by
  simp only [ordinaryOriginalProfile, ordinaryVerticalProfile, ordinaryChildPolynomial,
    eval_add, eval_C, ← AddCircle.coe_sub, ← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_pow]
  congr 1
  have h := ordinary_erase_eval D (P z.1) ((label z.2 : ℤ) : ℝ)
  nlinarith

/-- Even an exact top relation does not permit discarding its nonzero circle root.
This is an obstruction to a proposed descent shortcut, not a counterexample to P0. -/
theorem ordinary_child_zero_branch_obstruction (D N : ℕ) :
    OrdinaryTopRelation D 2 0 N ((1 / 2 : ℝ) : Frequency) ∧
      ‖(((monomial D (1 / 2) : ℝ[X]).eval 1 : ℝ) : Frequency) -
        (((ordinaryChildPolynomial D (monomial D (1 / 2)) 0).eval 1 : ℝ) : Frequency)‖ = 1 / 2 := by
  constructor
  · refine ⟨2, by norm_num, le_rfl, ?_⟩
    rw [zero_branch_division_counterexample.1]
    simp
  · have h : (monomial D (1 / 2) : ℝ[X]).eval 1 -
        (ordinaryChildPolynomial D (monomial D (1 / 2)) 0).eval 1 = 1 / 2 := by
      simpa only [ordinaryChildPolynomial, eval_add, eval_C, add_zero, coeff_monomial,
        if_pos rfl, ite_true, one_pow, mul_one] using ordinary_erase_eval D (monomial D (1 / 2)) 1
    rw [← AddCircle.coe_sub, h]
    exact zero_branch_division_counterexample.2

/-- Multiplication by the original vertical power converts the top relation to a cubic major arc. -/
theorem ordinary_increment_majorArc {N : ℕ} (hN : 0 < N) (D Q R : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hQR : Q ≤ R) (hER : E ≤ R) (a : Frequency) (y : Fin (N ^ 2))
    (ha : OrdinaryTopRelation D Q E N a) : MajorArc R N (((label y : ℤ) ^ D) • a) := by
  obtain ⟨q, hq, hqQ, hb⟩ := ha
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := hnR.ne'
  have hy : (label y : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast (Nat.succ_le_of_lt y.isLt)
  have hyp : (label y : ℝ) ^ D ≤ (N : ℝ) ^ (2 * D) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg (label y)) hy D
  have he : q • (((label y : ℤ) ^ D) • a) = (label y ^ D) • (q • a) := by
    rw [← Nat.cast_pow, natCast_zsmul]
    module
  refine ⟨q, hq, hqQ.trans hQR, ?_⟩
  rw [he]
  calc
    ‖(label y ^ D) • (q • a)‖ ≤ ((label y ^ D : ℕ) : ℝ) * ‖q • a‖ := norm_nsmul_le
    _ ≤ (label y : ℝ) ^ D * (E / (N : ℝ) ^ (2 * D + 3)) := by
      rw [Nat.cast_pow]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (N : ℝ) ^ (2 * D) * (E / (N : ℝ) ^ (2 * D + 3)) :=
      mul_le_mul_of_nonneg_right hyp (by positivity)
    _ = E / (N : ℝ) ^ 3 := by rw [pow_add]; field_simp
    _ ≤ (R : ℝ) / (N : ℝ) ^ 3 := div_le_div_of_nonneg_right hER (by positivity)

/-- Real representatives of the complete circle list give actual polynomial constant terms. -/
theorem majorArc_universal_real_list (Q : ℕ) (hQ : 0 < Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∀ N : ℕ, 0 < N → ∃ c : Fin J → ℝ,
      ∀ a : Frequency, MajorArc Q N a → ∃ i : Fin J,
        ‖a - (c i : Frequency)‖ ≤ ε / (2 * (N : ℝ) ^ 3) := by
  classical
  obtain ⟨J, hJ, hlist⟩ := majorArc_universal_circle_list Q hQ ε hε
  refine ⟨J, hJ, ?_⟩
  intro N hN
  obtain ⟨b, hb⟩ := hlist N hN
  choose c hc hnorm using fun i => exists_nearest_frequency_lift (b i)
  refine ⟨c, ?_⟩
  intro a ha
  obtain ⟨i, hi⟩ := hb a ha
  exact ⟨i, by simpa only [hc i] using hi⟩

/-- The child count and offsets precede degree and all original coefficients.
The assignment uses only the top field; no lower-coefficient or response resampling occurs. -/
theorem uniform_ordinary_lower_children (Q : ℕ) (hQ : 0 < Q) (E : ℝ) (hE : 0 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∀ N : ℕ, 0 < N → ∃ c : Fin J → ℝ,
      ∀ D : ℕ, ∀ a : Fin N → Frequency, ∃ j : Base N → Fin J,
        ∀ P : Fin N → ℝ[X], (∀ x, ((P x).coeff D : Frequency) = a x) →
          ∀ z : Base N, OrdinaryTopRelation D Q E N (a z.1) →
            ‖ordinaryOriginalProfile P z - ordinaryOriginalProfile
              (fun x => ordinaryChildPolynomial D (P x) (c (j z))) z‖ ≤
                ε / (2 * (N : ℝ) ^ 3) := by
  classical
  let R := max Q (Nat.ceil E)
  have hR : 0 < R := hQ.trans_le (le_max_left _ _)
  have hER : E ≤ (R : ℝ) := (Nat.le_ceil E).trans (by exact_mod_cast (le_max_right Q (Nat.ceil E)))
  obtain ⟨J, hJ, hgrid⟩ := majorArc_universal_real_list R hR ε hε
  refine ⟨J, hJ, ?_⟩
  intro N hN
  obtain ⟨c, hc⟩ := hgrid N hN
  refine ⟨c, ?_⟩
  intro D a
  have hp (z : Base N) : ∃ i : Fin J, OrdinaryTopRelation D Q E N (a z.1) →
      ‖((label z.2 : ℤ) ^ D) • a z.1 - (c i : Frequency)‖ ≤ ε / (2 * (N : ℝ) ^ 3) := by
    by_cases hz : OrdinaryTopRelation D Q E N (a z.1)
    · obtain ⟨i, hi⟩ := hc (((label z.2 : ℤ) ^ D) • a z.1)
        (ordinary_increment_majorArc hN D Q R E hE (le_max_left _ _) hER (a z.1) z.2 hz)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hJ⟩, fun h => (hz h).elim⟩
  choose j hj using hp
  refine ⟨j, ?_⟩
  intro P hP z hz
  rw [ordinary_child_error, hP]
  exact hj z hz

end GMZP0
