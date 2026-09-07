import GMZP0.MeanAlgebra
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! Finite Fourier inversion with probability-normalized coefficients and counting-measure synthesis. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def finiteFourier {G : Type*} [AddCommGroup G] [Fintype G]
    (F : G → ℂ) (ψ : AddChar G ℂ) : ℂ := complexUniformMean (fun x => F x * conj (ψ x))

theorem complexUniformMean_sum {I J : Type*} [Fintype I] [Fintype J] (F : I → J → ℂ) :
    complexUniformMean (fun i => ∑ j, F i j) = ∑ j, complexUniformMean (fun i => F i j) := by
  simp only [complexUniformMean, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]

theorem finite_character_pair_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (x y : G) : (∑ ψ : AddChar G ℂ, conj (ψ x) * ψ y) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  have he (ψ : AddChar G ℂ) : conj (ψ x) * ψ y = ψ (y - x) := by
    rw [ψ.map_sub_eq_div, div_eq_mul_inv, ψ.inv_apply_eq_conj]
    exact mul_comm _ _
  simp only [he, AddChar.sum_apply_eq_ite, sub_eq_zero, eq_comm]

theorem finiteFourier_inversion {G : Type*} [AddCommGroup G] [Fintype G]
    (F : G → ℂ) (y : G) : (∑ ψ : AddChar G ℂ, finiteFourier F ψ * ψ y) = F y := by
  classical
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = complexUniformMean (fun x => ∑ ψ : AddChar G ℂ, F x * (conj (ψ x) * ψ y)) := by
      simp only [finiteFourier, ← complexUniformMean_mul_const, ← complexUniformMean_sum, mul_assoc]
    _ = complexUniformMean (fun x => F x * (if x = y then (Fintype.card G : ℂ) else 0)) := by
      congr 1
      funext x
      rw [← Finset.mul_sum, finite_character_pair_sum]
    _ = F y := by
      simp only [complexUniformMean, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact mul_div_cancel_right₀ _ hn

end GMZP0
