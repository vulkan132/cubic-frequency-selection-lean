import GMZP0.MeanAlgebra

/-! An exact finite energy bound invariant under reindexing. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem finite_self_correlation_le {I : Type*} [Fintype I] (e : I ≃ I) (a : I → ℝ) :
    (∑ i, a i * a (e i)) ≤ ∑ i, a i ^ 2 := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset I))
    (fun i _ => show 2 * (a i * a (e i)) ≤ a i ^ 2 + a (e i) ^ 2 by
      nlinarith [sq_nonneg (a i - a (e i))])
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Equiv.sum_comp e (fun i => a i ^ 2)] at hs
  linarith

end GMZP0
