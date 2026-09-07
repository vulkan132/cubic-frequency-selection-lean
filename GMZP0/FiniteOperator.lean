import GMZP0.WeightedEnergy

/-! Exact finite input geometry and the operator-to-energy interface for the original response. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev InputBox (N : ℕ) := Fin (2 * N) × Fin (2 * N ^ 2)

def inputPoint {N : ℕ} (u : InputBox N) : ℤ × ℤ :=
  ((u.1.val : ℤ) + 1, (u.2.val : ℤ) + 1)

/-- Every original parabola endpoint lies in [2N] × [2N²]. -/
def endpointIndex {N : ℕ} (z : Base N) (r : Fin N) : InputBox N :=
  (⟨z.1.val + r.val + 1, by
      have hz := z.1.isLt
      have hr := r.isLt
      omega⟩,
   ⟨z.2.val + (r.val + 1) ^ 2, by
      have hz := z.2.isLt
      have hr : r.val + 1 ≤ N := Nat.succ_le_of_lt r.isLt
      have hsq : (r.val + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hr 2
      omega⟩)

/-- The finite input index represents the exact original integer endpoint. -/
theorem endpoint_eq_inputPoint {N : ℕ} (z : Base N) (r : Fin N) :
    endpoint z r = inputPoint (endpointIndex z r) := by
  apply Prod.ext <;> simp only [endpoint, basePoint, inputPoint, endpointIndex, label,
    Nat.cast_add, Nat.cast_one, Nat.cast_pow] <;> ring

@[simp] theorem card_inputBox (N : ℕ) : Fintype.card (InputBox N) = 4 * N ^ 3 := by
  simp only [InputBox, Fintype.card_prod, Fintype.card_fin]
  ring

def inputEnergy (N : ℕ) (f : ℤ × ℤ → ℂ) : ℝ :=
  ∑ u : InputBox N, ‖f (inputPoint u)‖ ^ 2

/-- The finite input energy bound uses the original one-bounded function. -/
theorem inputEnergy_le (N : ℕ) (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1) :
    inputEnergy N f ≤ 4 * (N : ℝ) ^ 3 := by
  calc
    inputEnergy N f ≤ ∑ _u : InputBox N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u _
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf (inputPoint u)) 2
    _ = 4 * (N : ℝ) ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, card_inputBox, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_one]

def finiteResponse (N : ℕ) (p : Base N → Frequency) (g : InputBox N → ℂ) (z : Base N) : ℂ :=
  (∑ r : Fin N, g (endpointIndex z r) * cubicPhase (p z) r) / (N : ℂ)

/-- Restricting f to the finite input box leaves every original complete response unchanged. -/
theorem finiteResponse_original (N : ℕ) (p : Base N → Frequency) (f : ℤ × ℤ → ℂ)
    (z : Base N) :
    finiteResponse N p (fun u => f (inputPoint u)) z = response N f z (p z) := by
  simp only [finiteResponse, response, endpoint_eq_inputPoint]

/-- The exact squared finite operator estimate needed at this interface; not an assumed theorem. -/
def FiniteMinorEstimate (Q N : ℕ) (s : ℝ) (p : Base N → Frequency) : Prop := by
  classical
  exact ∀ g : InputBox N → ℂ,
    (∑ z : Base N, if MajorArc Q N (p z) then 0 else ‖finiteResponse N p g z‖ ^ 2) ≤
      s ^ 2 * ∑ u : InputBox N, ‖g u‖ ^ 2

/-- A finite operator bound gives the unweighted energy bound for the same original f. -/
theorem profileMinorEnergy_of_finite_estimate (Q N : ℕ) (s : ℝ)
    (p : Base N → Frequency) (hestimate : FiniteMinorEstimate Q N s p)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1) :
    profileMinorEnergy Q N f p ≤ 4 * (N : ℝ) ^ 3 * s ^ 2 := by
  classical
  have h := hestimate (fun u => f (inputPoint u))
  simp only [finiteResponse_original] at h
  change profileMinorEnergy Q N f p ≤ s ^ 2 * inputEnergy N f at h
  calc
    profileMinorEnergy Q N f p ≤ s ^ 2 * inputEnergy N f := h
    _ ≤ s ^ 2 * (4 * (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (inputEnergy_le N f hf) (sq_nonneg _)
    _ = 4 * (N : ℝ) ^ 3 * s ^ 2 := by ring

/-- The original function, arbitrary assignment and original weight share the same energy bound. -/
theorem finite_estimates_assigned_energy {N J : ℕ} (hN : 0 < N) (Q : ℕ) (s : ℝ)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1)
    (p : Fin J → Base N → Frequency) (j : Base N → Fin J)
    (A : Finset (Base N)) (μ : Base N → ℝ)
    (hμ : ∀ z ∈ A, μ z ≤ (N : ℝ)⁻¹ ^ 3)
    (hestimates : ∀ i, FiniteMinorEstimate Q N s (p i)) :
    (∑ z ∈ minorPoints Q N (fun z => p (j z) z) A,
      μ z * ‖response N f z (p (j z) z)‖ ^ 2) ≤ 4 * (J : ℝ) * s ^ 2 := by
  exact assigned_minor_energy hN Q s f p j A μ hμ
    (fun i => profileMinorEnergy_of_finite_estimate Q N s (p i) (hestimates i) f hf)

end GMZP0
