import GMZP0.Response

/-! Finite-list selection with the original nonnegative weight. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- A finite nonempty list has an entry at least its mean. -/
theorem exists_ge_mean {J : Type*} [Fintype J] [Nonempty J] (v : J → ℝ) :
    ∃ j, (∑ i, v i) / (Fintype.card J : ℝ) ≤ v j := by
  have hc : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ _i : J, (∑ j, v j) / (Fintype.card J : ℝ)) ≤ ∑ j, v j := by
    simp [mul_div_cancel₀ _ hc]
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨j, hj⟩

/-- Arbitrary pointwise assignment still selects one column of positive original weight. -/
theorem finite_response_selection {Z J : Type*} [Fintype J] [Nonempty J]
    (A : Finset Z) (μ : Z → ℝ) (R : Z → J → ℝ) (j : Z → J) (t : ℝ)
    (hμ : ∀ z ∈ A, 0 ≤ μ z)
    (hR : ∀ z ∈ A, ∀ i, 0 ≤ R z i)
    (hselected : ∀ z ∈ A, t ≤ R z (j z)) :
    ∃ i, t * (∑ z ∈ A, μ z) / (Fintype.card J : ℝ) ≤
      ∑ z ∈ A, μ z * R z i := by
  classical
  have hsum : t * (∑ z ∈ A, μ z) ≤ ∑ i : J, ∑ z ∈ A, μ z * R z i := by
    calc
      t * (∑ z ∈ A, μ z) = ∑ z ∈ A, μ z * t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ ≤ ∑ z ∈ A, μ z * R z (j z) :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hselected z hz) (hμ z hz)
      _ ≤ ∑ z ∈ A, ∑ i : J, μ z * R z i := by
        apply Finset.sum_le_sum
        intro z hz
        exact Finset.single_le_sum (fun i _ => mul_nonneg (hμ z hz) (hR z hz i))
          (Finset.mem_univ (j z))
      _ = ∑ i : J, ∑ z ∈ A, μ z * R z i := Finset.sum_comm
  obtain ⟨i, hi⟩ := exists_ge_mean (fun i => ∑ z ∈ A, μ z * R z i)
  exact ⟨i, (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans hi⟩

/-- Terminal selection after capture has been supplied explicitly as hypotheses. -/
theorem original_response_of_finite_capture {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1)
    (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ)
    (β : Fin L → Frequency) (A : Finset (Base N)) (j : Base N → Fin L)
    (η ε : ℝ) (hμ : ∀ z ∈ A, 0 ≤ μ z)
    (hlam : ∀ z ∈ A, ‖lam z‖ = 1)
    (hresponse : ∀ z ∈ A, η ≤ (lam z * response N f z (θ z)).re)
    (hclose : ∀ z ∈ A, cubicDistance N (θ z) (β (j z)) ≤ ε) :
    ∃ i : Fin L, (η - ε) * (∑ z ∈ A, μ z) / (L : ℝ) ≤
      ∑ z ∈ A, μ z * ‖response N f z (β i)‖ := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hpoint : ∀ z ∈ A, η - ε ≤ ‖response N f z (β (j z))‖ := by
    intro z hz
    exact norm_response_transfer hN f hf z (θ z) (β (j z)) (lam z) (hlam z hz)
      η ε (hresponse z hz) (hclose z hz)
  simpa using finite_response_selection A μ (fun z i => ‖response N f z (β i)‖) j
    (η - ε) hμ (fun _ _ _ => norm_nonneg _) hpoint

/-- An original weight bounded by N⁻³ never exceeds the original box average. -/
theorem weighted_response_le_mean (N : ℕ) (f : ℤ × ℤ → ℂ) (β : Frequency)
    (A : Finset (Base N)) (μ : Base N → ℝ)
    (hμ : ∀ z ∈ A, μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    (∑ z ∈ A, μ z * ‖response N f z β‖) ≤ meanResponse N f (fun _ => β) := by
  calc
    (∑ z ∈ A, μ z * ‖response N f z β‖) ≤
        ∑ z ∈ A, (N : ℝ)⁻¹ ^ 3 * ‖response N f z β‖ := by
      exact Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hμ z hz) (norm_nonneg _)
    _ = (N : ℝ)⁻¹ ^ 3 * ∑ z ∈ A, ‖response N f z β‖ := (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ)⁻¹ ^ 3 * ∑ z : Base N, ‖response N f z β‖ := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_univ_sum_of_nonneg fun z => norm_nonneg _)
      positivity
    _ = meanResponse N f (fun _ => β) := by
      simp only [meanResponse, div_eq_mul_inv, inv_pow, mul_comm]

/-- Finite capture yields a constant response; capture itself is an explicit premise. -/
theorem captured_response_lower_bound {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1)
    (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ)
    (β : Fin L → Frequency) (A : Finset (Base N)) (j : Base N → Fin L)
    (η ε c : ℝ) (hε : ε ≤ η)
    (hμ : ∀ z ∈ A, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3)
    (hc : c ≤ ∑ z ∈ A, μ z)
    (hlam : ∀ z ∈ A, ‖lam z‖ = 1)
    (hresponse : ∀ z ∈ A, η ≤ (lam z * response N f z (θ z)).re)
    (hclose : ∀ z ∈ A, cubicDistance N (θ z) (β (j z)) ≤ ε) :
    ∃ b : Frequency, (η - ε) * c / (L : ℝ) ≤ meanResponse N f (fun _ => b) := by
  obtain ⟨i, hi⟩ := original_response_of_finite_capture hN hL f hf θ lam μ β A j η ε
    (fun z hz => (hμ z hz).1) hlam hresponse hclose
  refine ⟨β i, ?_⟩
  have hmass : (η - ε) * c / (L : ℝ) ≤ (η - ε) * (∑ z ∈ A, μ z) / (L : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hε))
      (Nat.cast_nonneg _)
  exact hmass.trans (hi.trans (weighted_response_le_mean N f (β i) A μ
    (fun z hz => (hμ z hz).2)))

/-- Every finite scale has an original frequency giving at least delta/N³.
This scale-dependent bound alone does not prove P0. -/
theorem small_scale_selection {N : ℕ} (hN : 0 < N) (f : ℤ × ℤ → ℂ)
    (θ : Base N → Frequency) (δ : ℝ) (hmean : δ ≤ meanResponse N f θ) :
    ∃ β : Frequency, δ / (N : ℝ) ^ 3 ≤ meanResponse N f (fun _ => β) := by
  let : Nonempty (Base N) := ⟨(⟨0, hN⟩, ⟨0, pow_pos hN 2⟩)⟩
  obtain ⟨z, hz⟩ := exists_ge_mean (fun z : Base N => ‖response N f z (θ z)‖)
  have hz' : δ ≤ ‖response N f z (θ z)‖ := by
    apply hmean.trans
    simpa only [meanResponse, card_base, Nat.cast_pow] using hz
  refine ⟨θ z, ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact hz'.trans (Finset.single_le_sum (fun w _ => norm_nonneg (response N f w (θ z)))
    (Finset.mem_univ z))

end GMZP0
