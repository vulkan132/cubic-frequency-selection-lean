import GMZP0.OriginalCubeWeyl

/-! Select successful cube coefficients while retaining every original cube weight. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem weighted_condition_mass {I : Type*} [Fintype I] [Nonempty I]
    (W R : I → ℝ) (P : I → Prop) [DecidablePred P] {γ : ℝ} (hγ : 0 < γ)
    (hW : ∀ i, 0 ≤ W i ∧ W i ≤ 1) (hR : ∀ i, R i ≤ 1)
    (hlarge : γ ≤ realUniformMean (fun i => W i * R i))
    (hcondition : ∀ i, γ / 2 ≤ R i → P i) :
    γ / 2 ≤ realUniformMean (fun i => if P i then W i else 0) := by
  classical
  have hpoint (i : I) : W i * R i ≤ (if P i then W i else 0) + γ / 2 := by
    by_cases hi : P i
    · rw [if_pos hi]
      have hh := mul_le_mul_of_nonneg_left (hR i) (hW i).1
      linarith
    · rw [if_neg hi]
      have hr : R i ≤ γ / 2 := le_of_lt (lt_of_not_ge (fun hh => hi (hcondition i hh)))
      have hh := mul_le_mul_of_nonneg_left hr (hW i).1
      have hh' := mul_le_mul_of_nonneg_right (hW i).2 (by positivity : 0 ≤ γ / 2)
      linarith
  have hmean := realUniformMean_mono _ _ hpoint
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : realUniformMean (fun i => (if P i then W i else 0) + γ / 2) =
      realUniformMean (fun i => if P i then W i else 0) + γ / 2 := by
    simp only [realUniformMean, Finset.sum_add_distrib, add_div, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hn]
  rw [he] at hmean
  linarith

def cyclicCubeNearMass (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (D : ℕ) (E : ℝ) : ℝ :=
  realUniformMean (fun z : CubeWeylParameters N q ℓ =>
    if ‖D • cyclicCubeCubicCoeff N q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.2‖ ≤ E / (N : ℝ) ^ 3
    then cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 z.2.1.val z.2.2.2.2 else 0)

theorem uniform_weighted_cube_weyl (γ : ℝ) (hγ : 0 < γ) :
    ∃ D : ℕ, ∃ E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ (q : ℕ) [NeZero q], ∀ ℓ : ℕ,
      ∀ (p : Base N → Frequency) (σ : Base N → ℝ),
        (∀ z, 0 ≤ σ z ∧ σ z ≤ 1) → γ ≤ cyclicWeightedTimeNorm N q ℓ p σ →
          γ / 2 ≤ cyclicCubeNearMass N q ℓ p σ D E := by
  obtain ⟨D, E, hD, hE, hw⟩ := uniform_original_cube_weyl (γ / 2) (by positivity)
  refine ⟨D, E, hD, hE, ?_⟩
  intro N hN q _ ℓ p σ hσ hlarge
  have hq : 0 < q := NeZero.pos q
  have hcard : 0 < Fintype.card (CubeWeylParameters N q ℓ) := by
    rw [card_cubeWeylParameters]
    positivity
  let : Nonempty (CubeWeylParameters N q ℓ) := Fintype.card_pos_iff.mp hcard
  apply weighted_condition_mass
    (fun z : CubeWeylParameters N q ℓ => cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 z.2.1.val z.2.2.2.2)
    (fun z : CubeWeylParameters N q ℓ =>
      ‖cyclicCubeTimeAverage N q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.1.val z.2.2.2.2‖)
    _ hγ (fun z => cyclicCubeWeight_bounds N q ℓ σ z.1 z.2.2.1 z.2.1.val z.2.2.2.2 hσ)
    (fun z => cyclicCubeTimeAverage_norm_le hN q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.1.val z.2.2.2.2)
    hlarge
  intro z hz
  exact hw N hN q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.1.val z.2.2.2.2 hz

end GMZP0
