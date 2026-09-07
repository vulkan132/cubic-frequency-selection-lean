import GMZP0.Response

/-! Full-label metric properties, with no selected subset of labels. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- Minkowski's inequality for finite Euclidean sums, from Cauchy–Schwarz. -/
theorem root_sum_square_add_le {Z : Type*} [Fintype Z] (v w : Z → ℝ) :
    Real.sqrt (∑ z, (v z + w z) ^ 2) ≤
      Real.sqrt (∑ z, v z ^ 2) + Real.sqrt (∑ z, w z ^ 2) := by
  have hv := Real.sq_sqrt (Finset.sum_nonneg (fun z (_ : z ∈ (Finset.univ : Finset Z)) => sq_nonneg (v z)))
  have hw := Real.sq_sqrt (Finset.sum_nonneg (fun z (_ : z ∈ (Finset.univ : Finset Z)) => sq_nonneg (w z)))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v w
  have hexpand : (∑ z, (v z + w z) ^ 2) =
      (∑ z, v z ^ 2) + 2 * (∑ z, v z * w z) + ∑ z, w z ^ 2 := by
    calc
      (∑ z, (v z + w z) ^ 2) = ∑ z, (v z ^ 2 + 2 * (v z * w z) + w z ^ 2) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
  nlinarith

@[simp] theorem cubicDistance_self (N : ℕ) (a : Frequency) : cubicDistance N a a = 0 := by
  simp [cubicDistance, cubicDistanceSq]

theorem cubicDistance_symm (N : ℕ) (a b : Frequency) :
    cubicDistance N a b = cubicDistance N b a := by
  simp only [cubicDistance, cubicDistanceSq, norm_sub_rev]

/-- Triangle inequality for the actual average over all N cubic labels. -/
theorem cubicDistance_triangle (N : ℕ) (a b c : Frequency) :
    cubicDistance N a c ≤ cubicDistance N a b + cubicDistance N b c := by
  have hpoint (r : Fin N) : ‖cubicPhase a r - cubicPhase c r‖ ≤
      ‖cubicPhase a r - cubicPhase b r‖ + ‖cubicPhase b r - cubicPhase c r‖ := by
    simpa only [sub_add_sub_cancel] using
      norm_add_le (cubicPhase a r - cubicPhase b r) (cubicPhase b r - cubicPhase c r)
  have hsq : (∑ r : Fin N, ‖cubicPhase a r - cubicPhase c r‖ ^ 2) ≤
      ∑ r : Fin N, (‖cubicPhase a r - cubicPhase b r‖ + ‖cubicPhase b r - cubicPhase c r‖) ^ 2 := by
    apply Finset.sum_le_sum
    intro r _
    exact pow_le_pow_left₀ (norm_nonneg _) (hpoint r) 2
  unfold cubicDistance cubicDistanceSq
  simp only [Real.sqrt_div' _ (Nat.cast_nonneg N)]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (Real.sqrt_le_sqrt hsq).trans (root_sum_square_add_le _ _)

/-- A pointwise chord bound controls the full-label distance. -/
theorem cubicDistance_le_of_label_bound {N : ℕ} (hN : 0 < N)
    (a b : Frequency) (E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ r : Fin N, ‖cubicPhase a r - cubicPhase b r‖ ≤ E) :
    cubicDistance N a b ≤ E := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (Real.sqrt_le_left hE).2
  unfold cubicDistanceSq
  apply (div_le_iff₀ hNr).2
  calc
    (∑ r : Fin N, ‖cubicPhase a r - cubicPhase b r‖ ^ 2) ≤ ∑ _r : Fin N, E ^ 2 :=
      Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (norm_nonneg _) (hbound r) 2
    _ = E ^ 2 * (N : ℝ) := by simp [mul_comm]

end GMZP0
