import GMZP0.OrdinaryFreezing
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Localization.Integer

/-! Integer leading-coefficient functionals whose constants depend only on relative nodes. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace GMZP0

/-- For fixed relative integer nodes, one integer functional works at every integer center.
Denominators are cleared before the center is chosen. -/
theorem integer_monomial_interpolation (D : ℕ) (v : Fin (D + 1) → ℤ) (hv : Function.Injective v) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ c : Fin (D + 1) → ℤ,
      ∀ H : ℤ, ∑ i, c i * (H + v i) ^ D = q := by
  classical
  let w (i : Fin (D + 1)) : ℚ := (∏ j ∈ Finset.univ.erase i, ((v i : ℚ) - v j))⁻¹
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ w
  have hq0 : (q : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp q.property
  have hc0 (i : Fin (D + 1)) : ∃ c : ℤ, (c : ℚ) = (q : ℤ) • w i := hq i (Finset.mem_univ _)
  choose c hc using hc0
  refine ⟨q, hq0, c, ?_⟩
  intro H
  have hvQ : Set.InjOn (fun i => (v i : ℚ)) (Finset.univ : Finset (Fin (D + 1))) := by
    intro i _ j _ he
    change (v i : ℚ) = (v j : ℚ) at he
    exact hv (by exact_mod_cast he)
  have hdeg : ((X + C (H : ℚ)) ^ D).degree <
      (((Finset.univ : Finset (Fin (D + 1))).card : ℕ) : WithBot ℕ) := by
    simp only [degree_pow, degree_X_add_C, Finset.card_univ, Fintype.card_fin, nsmul_one]
    exact_mod_cast Nat.lt_succ_self D
  have hcoeff := Lagrange.coeff_eq_sum hvQ hdeg
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, coeff_X_add_C_pow,
    Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
    eval_pow, eval_add, eval_X, eval_C] at hcoeff
  have hid : ∑ i, w i * ((H : ℚ) + v i) ^ D = 1 := by
    simpa only [w, div_eq_mul_inv, add_comm, mul_comm] using hcoeff.symm
  have he : (∑ i, (c i : ℚ) * (((H + v i : ℤ) : ℚ) ^ D)) = (q : ℤ) := by
    simp_rw [hc]
    simp only [zsmul_eq_mul, Int.cast_add]
    calc
      _ = ((q : ℤ) : ℚ) * ∑ i, w i * ((H : ℚ) + v i) ^ D := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hid, mul_one]
  exact_mod_cast he

/-- Finitely many relative node patterns give a uniform positive denominator and coefficient bound.
The center H, circle coefficient and return error are chosen only afterwards. -/
theorem uniform_monomial_pattern_seed (D L : ℕ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ v : Fin (D + 1) → Fin L, Function.Injective v →
      ∀ H : ℤ, ∀ a : Frequency, ∀ ε : ℝ, 0 ≤ ε →
        (∀ i, ‖((H + (v i : ℤ)) ^ D) • a‖ ≤ ε) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ (Q : ℝ) * ε := by
  classical
  have hex (v : Fin (D + 1) → Fin L) : ∃ q : ℤ, ∃ c : Fin (D + 1) → ℤ,
      q ≠ 0 ∧ (Function.Injective v → ∀ H : ℤ, ∑ i, c i * (H + (v i : ℤ)) ^ D = q) := by
    by_cases hv : Function.Injective v
    · have hz : Function.Injective (fun i => (v i : ℤ)) := by
        intro i j he
        apply hv
        apply Fin.ext
        change ((v i).val : ℤ) = ((v j).val : ℤ) at he
        exact_mod_cast he
      obtain ⟨q, hq, c, hc⟩ := integer_monomial_interpolation D (fun i => (v i : ℤ)) hz
      exact ⟨q, c, hq, fun _ => hc⟩
    · exact ⟨1, fun _ => 0, one_ne_zero, fun h => (hv h).elim⟩
  choose q c hq hc using hex
  let B (v : Fin (D + 1) → Fin L) := (q v).natAbs + ∑ i, (c v i).natAbs
  let Q := (∑ v, B v) + 1
  have hB (v : Fin (D + 1) → Fin L) : B v ≤ Q := by
    have hh : B v ≤ ∑ w, B w := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    exact hh.trans (Nat.le_succ _)
  refine ⟨Q, by dsimp [Q]; omega, ?_⟩
  intro v hv H a ε hε hr
  have hqQ : (q v).natAbs ≤ Q := (Nat.le_add_right _ _).trans (hB v)
  have hcQ : (∑ i, (c v i).natAbs) ≤ Q := (Nat.le_add_left _ _).trans (hB v)
  have he : (q v) • a = ∑ i, (c v i) • (((H + (v i : ℤ)) ^ D) • a) := by
    rw [← hc v hv H, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_smul _ _ _
  refine ⟨(q v).natAbs, Int.natAbs_pos.mpr (hq v), hqQ, ?_⟩
  rw [norm_natAbs_smul, he]
  calc
    _ ≤ ∑ i, ‖(c v i) • (((H + (v i : ℤ)) ^ D) • a)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((c v i).natAbs : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← norm_natAbs_smul]
      exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_left (hr i) (Nat.cast_nonneg _))
    _ = ((∑ i, (c v i).natAbs : ℕ) : ℝ) * ε := by rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (Q : ℝ) * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hcQ) hε

end GMZP0
