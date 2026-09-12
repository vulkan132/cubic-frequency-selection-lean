import GMZP0.AffineTopRelation

/-! The no-relation part of the actual affine-profile operator has a uniform small norm. -/
noncomputable section
namespace GMZP0

/-- Every unrestricted real affine profile in the manuscript has exactly this circle-valued integer evaluation. -/
theorem affineVerticalProfile_real_eval {N : ℕ} (a b : Fin N → ℝ) (x : Fin N) (y : ℤ) :
    affineVerticalProfile (fun x => (a x : Frequency)) (fun x => (b x : Frequency)) x y =
      (((y : ℝ) * a x + b x : ℝ) : Frequency) := by
  rw [affineVerticalProfile, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
  rw [zsmul_eq_mul]

/-- If an entire original output row vanishes, its actual Gram blocks cannot be large. -/
theorem largeBlockNeighbors_empty_of_zero_row {N : ℕ} {Y U : Type*} [Fintype Y] [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N)) (v : ℝ) (x : Fin N)
    (hz : ∀ y u, K (x, y) u = 0) : largeBlockNeighbors K H v x = ∅ := by
  classical
  have hb (x' : Fin N) : KernelEnergyBound (blockGramKernel K x x') (v / N) := by
    intro g
    have he : kernelAction (blockGramKernel K x x') g = fun _ => 0 := by
      funext y
      simp [kernelAction, blockGramKernel, gramKernel, hz]
    rw [he]
    simpa only [finiteEnergy, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using
      mul_nonneg (sq_nonneg (v / (N : ℝ))) (finiteEnergy_nonneg g)
  simp [largeBlockNeighbors, hb]

/-- Actual affine masks supported outside top-slope relations have uniformly small operator energy. -/
theorem uniform_affine_no_relation_operator (s : ℝ) (hs : 0 < s) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency, ∀ m : Base N → ℂ,
      (∀ z, ‖m z‖ ≤ 1) →
      (∀ x : Fin N, AffineTopRelation Q E N (a x) → ∀ y, m (x, y) = 0) →
      ∀ g : InputBox N → ℂ,
        finiteEnergy (fun z => m z * finiteResponse N (affineOriginalProfile a b) g z) ≤
          s ^ 2 * finiteEnergy g := by
  classical
  obtain ⟨ρ, v, hρ, hv, N₁, hN₁, hbudget⟩ := uniform_compressed_block_error_budget s hs
  obtain ⟨Q, E, N₂, hQ, hE, hN₂, hcount⟩ := uniform_affine_no_relation_count v ρ hv hρ
  refine ⟨Q, E, max N₁ N₂, hQ, hE, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN a b m hm hsupport g
  have hn : 0 < N := hN₁.trans_le ((le_max_left _ _).trans hN)
  have hc : ∀ x ∈ (Finset.univ : Finset (Fin N)),
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m)
        Finset.univ v x).card : ℝ) ≤ ρ * N := by
    intro x _
    by_cases hx : AffineTopRelation Q E N (a x)
    · rw [largeBlockNeighbors_empty_of_zero_row _ _ _ _ (fun y u => by
        simp only [outputMaskedKernel, hsupport x hx y, zero_mul])]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · exact (hcount N ((le_max_right _ _).trans hN) a b m hm x hx).le
  have hb := masked_original_energy_of_few_large_blocks hn (affineOriginalProfile a b) m
    Finset.univ hm (by simp) v ρ hv.le hρ.le hc g
  exact hb.trans (mul_le_mul_of_nonneg_right (hbudget N ((le_max_left _ _).trans hN))
    (finiteEnergy_nonneg g))

/-- Remove precisely the rows with a top-slope relation, retaining any original pointwise mask. -/
def affineNoRelationMask {N : ℕ} (Q : ℕ) (E : ℝ) (a : Fin N → Frequency)
    (m : Base N → ℂ) (z : Base N) : ℂ := by
  classical
  exact if AffineTopRelation Q E N (a z.1) then 0 else m z

/-- The exact no-relation mask remains pointwise contractive. -/
theorem affineNoRelationMask_bound {N : ℕ} (Q : ℕ) (E : ℝ) (a : Fin N → Frequency)
    (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1) : ∀ z, ‖affineNoRelationMask Q E a m z‖ ≤ 1 := by
  intro z
  unfold affineNoRelationMask
  split_ifs <;> simp [hm z]

/-- The original masked response on no-relation rows satisfies the proved uniform error budget. -/
theorem uniform_affine_no_relation_mask_energy (s : ℝ) (hs : 0 < s) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency, ∀ m : Base N → ℂ,
      (∀ z, ‖m z‖ ≤ 1) → ∀ g : InputBox N → ℂ,
      finiteEnergy (fun z => affineNoRelationMask Q E a m z *
        finiteResponse N (affineOriginalProfile a b) g z) ≤ s ^ 2 * finiteEnergy g := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hb⟩ := uniform_affine_no_relation_operator s hs
  refine ⟨Q, E, N₀, hQ, hE, hN₀, ?_⟩
  intro N hN a b m hm g
  exact hb N hN a b (affineNoRelationMask Q E a m) (affineNoRelationMask_bound Q E a m hm)
    (fun x hx y => by simp only [affineNoRelationMask, hx, if_true]) g

end GMZP0
