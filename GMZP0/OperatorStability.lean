import GMZP0.OriginalBlockSchur

/-! Stability of the actual complete finite response, with arbitrary pointwise masks. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The complete finite original operator is a contraction for every frequency field. -/
theorem finiteResponse_energy_le {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (g : InputBox N → ℂ) :
    finiteEnergy (finiteResponse N p g) ≤ finiteEnergy g := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hrow (x : Fin N) : (∑ _x' : Fin N, (N : ℝ)⁻¹) ≤ 1 := by
    simp [hn]
  have h := kernel_action_energy_of_block_rows (responseKernel N p) (fun _ _ => (N : ℝ)⁻¹)
    (fun _ _ => by positivity) (fun _ _ => rfl) (original_horizontal_block_bound hN p)
    1 zero_le_one hrow g
  simpa only [finiteEnergy, responseKernel_action, one_mul] using h

/-- Positive averaging uses exactly the original endpoint and label set. -/
def positiveFiniteAverage (N : ℕ) (g : InputBox N → ℝ) (z : Base N) : ℝ :=
  (∑ r : Fin N, g (endpointIndex z r)) / (N : ℝ)

/-- Nonnegative original inputs have a nonnegative positive average. -/
theorem positiveFiniteAverage_nonneg (N : ℕ) (g : InputBox N → ℝ)
    (hg : ∀ u, 0 ≤ g u) (z : Base N) : 0 ≤ positiveFiniteAverage N g z := by
  exact div_nonneg (Finset.sum_nonneg (fun r _ => hg (endpointIndex z r))) (Nat.cast_nonneg N)

/-- Zero frequency on the norm of the same input is the positive original average. -/
theorem finiteResponse_zero_norm_input (N : ℕ) (g : InputBox N → ℂ) (z : Base N) :
    finiteResponse N (fun _ => 0) (fun u => (‖g u‖ : ℂ)) z =
      (positiveFiniteAverage N (fun u => ‖g u‖) z : ℂ) := by
  simp [finiteResponse, positiveFiniteAverage, Complex.ofReal_div, Complex.ofReal_sum]

/-- Positive averaging of the same input norms is a finite energy contraction. -/
theorem positiveFiniteAverage_energy_le {N : ℕ} (hN : 0 < N) (g : InputBox N → ℂ) :
    (∑ z, positiveFiniteAverage N (fun u => ‖g u‖) z ^ 2) ≤ finiteEnergy g := by
  have h := finiteResponse_energy_le hN (fun _ => 0) (fun u => (‖g u‖ : ℂ))
  simpa only [finiteEnergy, finiteResponse_zero_norm_input, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, abs_norm] using h

/-- A per-label phase error dominates the original response difference by positive averaging. -/
theorem finiteResponse_difference_le_average {N : ℕ}
    (p q : Base N → Frequency) (g : InputBox N → ℂ) (z : Base N) (ε : ℝ)
    (hphase : ∀ r : Fin N, ‖cubicPhase (p z) r - cubicPhase (q z) r‖ ≤ ε) :
    ‖finiteResponse N p g z - finiteResponse N q g z‖ ≤
      ε * positiveFiniteAverage N (fun u => ‖g u‖) z := by
  have he : finiteResponse N p g z - finiteResponse N q g z =
      (∑ r : Fin N, g (endpointIndex z r) * (cubicPhase (p z) r - cubicPhase (q z) r)) / (N : ℂ) := by
    simp only [finiteResponse, ← sub_div, mul_sub, Finset.sum_sub_distrib]
  rw [he, norm_div, Complex.norm_natCast]
  calc
    _ ≤ (∑ r : Fin N, ‖g (endpointIndex z r) * (cubicPhase (p z) r - cubicPhase (q z) r)‖) / (N : ℝ) :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg N)
    _ ≤ (∑ r : Fin N, ε * ‖g (endpointIndex z r)‖) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (hphase r) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_div_assoc]; rfl

/-- Closeness is needed only at points where the actual output mask is nonzero. -/
theorem masked_response_difference_energy {N : ℕ} (hN : 0 < N)
    (p q : Base N → Frequency) (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hphase : ∀ z, m z ≠ 0 → ∀ r : Fin N, ‖cubicPhase (p z) r - cubicPhase (q z) r‖ ≤ ε)
    (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * (finiteResponse N p g z - finiteResponse N q g z)) ≤
      ε ^ 2 * finiteEnergy g := by
  have hp (z : Base N) : ‖m z * (finiteResponse N p g z - finiteResponse N q g z)‖ ≤
      ε * positiveFiniteAverage N (fun u => ‖g u‖) z := by
    by_cases hz : m z = 0
    · simp only [hz, zero_mul, norm_zero]
      exact mul_nonneg hε (positiveFiniteAverage_nonneg N _ (fun u => norm_nonneg _) z)
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hm z) (norm_nonneg _)).trans
        (by simpa only [one_mul] using finiteResponse_difference_le_average p q g z ε (hphase z hz))
  calc
    _ ≤ ∑ z, (ε * positiveFiniteAverage N (fun u => ‖g u‖) z) ^ 2 :=
      Finset.sum_le_sum (fun z _ => pow_le_pow_left₀ (norm_nonneg _) (hp z) 2)
    _ = ε ^ 2 * ∑ z, positiveFiniteAverage N (fun u => ‖g u‖) z ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (positiveFiniteAverage_energy_le hN g) (sq_nonneg ε)

/-- The natural circle error controls every original label separately. -/
theorem cubicPhase_le_of_scaled_circle_error {N : ℕ} (hN : 0 < N)
    (a b : Frequency) (ε : ℝ) (hclose : ‖a - b‖ ≤ ε / (2 * Real.pi * (N : ℝ) ^ 3))
    (r : Fin N) : ‖cubicPhase a r - cubicPhase b r‖ ≤ ε := by
  have hr : (label r : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt r.isLt
  have hs : 0 < 2 * Real.pi * (N : ℝ) ^ 3 := by positivity
  calc
    _ ≤ 2 * Real.pi * (label r : ℝ) ^ 3 * ‖a - b‖ := cubicPhase_chord_le a b r
    _ ≤ 2 * Real.pi * (N : ℝ) ^ 3 * ‖a - b‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hr 3) (by positivity)) (norm_nonneg _)
    _ ≤ ε := by simpa only [mul_comm] using (le_div_iff₀ hs).mp hclose

/-- A supported circle approximation gives the true finite operator error on the same input. -/
theorem masked_response_circle_stability {N : ℕ} (hN : 0 < N)
    (p q : Base N → Frequency) (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ z, m z ≠ 0 → ‖p z - q z‖ ≤ ε / (2 * Real.pi * (N : ℝ) ^ 3))
    (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * (finiteResponse N p g z - finiteResponse N q g z)) ≤
      ε ^ 2 * finiteEnergy g :=
  masked_response_difference_energy hN p q m hm ε hε
    (fun z hz r => cubicPhase_le_of_scaled_circle_error hN (p z) (q z) ε (hclose z hz) r) g

end GMZP0
