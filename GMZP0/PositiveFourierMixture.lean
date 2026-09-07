import GMZP0.MeanAlgebra

/-! The finite nonnegative-coefficient estimate needed after the mixed cube inequality. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem positive_product_sum {I : Type*} [Fintype I] (d : ℕ) (w : I → ℝ) :
    (∑ v : Fin d → I, ∏ i, w (v i)) = (∑ j, w j) ^ d := by
  rw [← Fintype.prod_sum (fun (_ : Fin d) (j : I) => w j)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem positive_product_mixture_bound {I : Type*} [Fintype I] (d : ℕ)
    (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (C L : ℝ) (hs : (∑ j, w j) ≤ C)
    (hL : 0 ≤ L) (T : (Fin d → I) → ℂ) (hT : ∀ v, ‖T v‖ ≤ L) :
    ‖∑ v : Fin d → I, ((∏ i, w (v i) : ℝ) : ℂ) * T v‖ ≤ C ^ d * L := by
  classical
  have hp (v : Fin d → I) : 0 ≤ ∏ i, w (v i) := Finset.prod_nonneg (fun i _ => hw _)
  calc
    _ ≤ ∑ v : Fin d → I, ‖((∏ i, w (v i) : ℝ) : ℂ) * T v‖ := norm_sum_le _ _
    _ ≤ ∑ v : Fin d → I, (∏ i, w (v i)) * L := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp v)]
      exact mul_le_mul_of_nonneg_left (hT v) (hp v)
    _ = (∑ j, w j) ^ d * L := by rw [← Finset.sum_mul, positive_product_sum]
    _ ≤ C ^ d * L := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => hw _)) hs d) hL

end GMZP0
