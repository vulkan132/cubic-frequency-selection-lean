import GMZP0.CubeExpansion
import Mathlib.Algebra.Module.BigOperators

/-! Exact weighted character products and cubic coefficients on the circle. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem circleCharacter_sum {I : Type*} (s : Finset I) (F : I → Frequency) :
    circleCharacter (∑ i ∈ s, F i) = ∏ i ∈ s, circleCharacter (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleCharacter]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      circleCharacter_add, ih]

theorem alternating_weighted_character_product (d : ℕ) (σ : (Fin d → Bool) → ℝ)
    (lam : (Fin d → Bool) → ℂ) (p : (Fin d → Bool) → Frequency) :
    (∏ ω, cubeConj d ω ((σ ω : ℂ) * conj (lam ω) * circleCharacter (p ω))) =
      ((∏ ω, σ ω : ℝ) : ℂ) * (∏ ω, cubeConj d ω (conj (lam ω))) *
        circleCharacter (∑ ω, cubeSign d ω • p ω) := by
  rw [circleCharacter_sum]
  simp only [cubeConj_mul, cubeConj_ofReal, cubeConj_character, Finset.prod_mul_distrib,
    Complex.ofReal_prod]

theorem circle_cubic_translate (e d t : ℤ) (p : Frequency) :
    e • (-((t + d) ^ 3 • p)) =
      t ^ 3 • ((-e) • p) + t ^ 2 • ((-3 * e * d) • p) +
        t • ((-3 * e * d ^ 2) • p) + (-e * d ^ 3) • p := by
  simp only [← neg_zsmul, ← mul_zsmul, ← add_zsmul]
  congr 1
  ring

theorem circle_cubic_sum {I : Type*} [Fintype I] (e d : I → ℤ) (p : I → Frequency) (t : ℤ) :
    (∑ i, e i • (-((t + d i) ^ 3 • p i))) =
      t ^ 3 • (∑ i, (-e i) • p i) + t ^ 2 • (∑ i, (-3 * e i * d i) • p i) +
        t • (∑ i, (-3 * e i * d i ^ 2) • p i) + ∑ i, (-e i * d i ^ 3) • p i := by
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact circle_cubic_translate (e i) (d i) t (p i)

end GMZP0
