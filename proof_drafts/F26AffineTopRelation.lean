import GMZP0.AffineBlockRelations

/-! Actual large-neighbor counts force a uniform N^(-5) affine slope relation. -/
noncomputable section
namespace GMZP0

/-- Horizontal target points and their signed displacements are in exact one-to-one correspondence. -/
theorem horizontalGap_injective_right {N : ℕ} (x : Fin N) : Function.Injective (horizontalGap x) := by
  intro x' x'' he
  apply Fin.ext
  simp only [horizontalGap] at he
  omega

/-- The slope relation keeps a positive bounded integer multiplier and the full N^(-5) scale. -/
def AffineTopRelation (Q : ℕ) (E : ℝ) (N : ℕ) (a : Frequency) : Prop :=
  ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ 5

/-- Many actual compressed blocks force a top-slope relation, uniformly before all profile data. -/
theorem uniform_affine_many_blocks_top_relation (v ρ : ℝ) (hv : 0 < v) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency, ∀ m : Base N → ℂ,
      (∀ z, ‖m z‖ ≤ 1) → ∀ x : Fin N,
      ρ * (N : ℝ) ≤ (largeBlockNeighbors
        (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m) Finset.univ v x).card →
      AffineTopRelation Q E N (a x) := by
  classical
  obtain ⟨D, C, N₁, hD, hC, hN₁, hb⟩ := uniform_affine_block_row_relation v hv
  obtain ⟨Q, E, N₂, hQ, hE, hN₂, hr⟩ := uniform_bounded_multiplier_affine_returns ρ C hρ hC D hD
  refine ⟨Q, E, max N₁ N₂, hQ, hE, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN a b m hm x hcount
  let S := largeBlockNeighbors (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m)
    Finset.univ v x
  let T := S.image (horizontalGap x)
  have hT : T ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro h hh
    obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp hh
    have hgap := abs_lt.mp (horizontalGap_bound x x')
    exact Finset.mem_Icc.mpr ⟨hgap.1.le, hgap.2.le⟩
  have hcard : T.card = S.card := Finset.card_image_of_injective _ (horizontalGap_injective_right x)
  have hd : ρ * (N : ℝ) ≤ T.card := by rw [hcard]; exact hcount
  have hp : ∀ h ∈ T, ∃ d : ℕ, 0 < d ∧ d ≤ D ∧ ‖d • (h • a x + 0)‖ ≤ C / (N : ℝ) ^ 4 := by
    intro h hh
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hh
    have hx : x' ≠ x ∧ ¬ KernelEnergyBound (blockGramKernel
        (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m) x x') (v / N) := by
      simpa only [S, largeBlockNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hx'
    simpa only [add_zero] using hb N ((le_max_left _ _).trans hN) a b m hm x x' hx.1.symm hx.2
  exact hr 4 (by norm_num) N ((le_max_right _ _).trans hN) (a x) 0 T hT hd hp

/-- Failure of the slope relation forces strictly fewer than rho*N actual large compressed blocks. -/
theorem uniform_affine_no_relation_count (v ρ : ℝ) (hv : 0 < v) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency, ∀ m : Base N → ℂ,
      (∀ z, ‖m z‖ ≤ 1) → ∀ x : Fin N, ¬ AffineTopRelation Q E N (a x) →
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m)
        Finset.univ v x).card : ℝ) < ρ * N := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, ht⟩ := uniform_affine_many_blocks_top_relation v ρ hv hρ
  refine ⟨Q, E, N₀, hQ, hE, hN₀, ?_⟩
  intro N hN a b m hm x hx
  exact lt_of_not_ge (fun hc => hx (ht N hN a b m hm x hc))

end GMZP0
