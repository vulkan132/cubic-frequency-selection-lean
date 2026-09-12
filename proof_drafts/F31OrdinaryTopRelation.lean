import GMZP0.OrdinaryChildren
import GMZP0.OrdinaryBlockRelations
import GMZP0.MonomialReturnInterface

/-! Actual higher-degree block counts and no-relation energy, conditional on the
explicit leading Weyl input and the still-unproved INTERNAL monomial-return obligation. -/
noncomputable section
open Polynomial
namespace GMZP0

/-- Many actual compressed blocks give the current row's full top relation.
The external Weyl premise and the internal nonlinear-return premise are separate. -/
theorem uniform_ordinary_many_blocks_top_relation (hW : PolynomialLeadingWeylInput)
    (hR : MonomialDenseReturns) (D : ℕ) (hD : 2 ≤ D)
    (v ρ : ℝ) (hv : 0 < v) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℝ[X], (∀ x, (P x).natDegree ≤ D) →
      ∀ m : Base N → ℂ, (∀ z, ‖m z‖ ≤ 1) → ∀ x : Fin N,
      ρ * (N : ℝ) ≤ (largeBlockNeighbors
        (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m) Finset.univ v x).card →
      OrdinaryTopRelation D Q E N ((P x).coeff D : Frequency) := by
  classical
  obtain ⟨B, C, N₁, hB, hC, hN₁, hb⟩ := uniform_ordinary_block_row_relation hW D hD v hv
  obtain ⟨Q, E, N₂, hQ, hE, hN₂, hr⟩ := uniform_bounded_multiplier_monomial_returns
    hR D (D + 3) (by omega) (by omega) ρ C hρ hC B hB
  refine ⟨Q, E, max N₁ N₂, hQ, hE, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN P hP m hm x hcount
  let S := largeBlockNeighbors (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m)
    Finset.univ v x
  let T := S.image (horizontalGap x)
  have hmember (x' : Fin N) (hx' : x' ∈ S) :
      x' ≠ x ∧ ¬ KernelEnergyBound (blockGramKernel
        (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m) x x') (v / N) := by
    simpa only [S, largeBlockNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hx'
  have hT : T ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro h hh
    obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp hh
    have hgap := abs_lt.mp (horizontalGap_bound x x')
    exact Finset.mem_Icc.mpr ⟨hgap.1.le, hgap.2.le⟩
  have hnonzero : ∀ h ∈ T, h ≠ 0 := by
    intro h hh hz
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hh
    apply (hmember x' hx').1
    apply Fin.ext
    simp only [horizontalGap] at hz
    omega
  have hcard : T.card = S.card := Finset.card_image_of_injective _ (horizontalGap_injective_right x)
  have hd : ρ * (N : ℝ) ≤ T.card := by rw [hcard]; exact hcount
  have hp : ∀ h ∈ T, ∃ b : ℕ, 0 < b ∧ b ≤ B ∧
      ‖b • ((h ^ D) • ((P x).coeff D : Frequency))‖ ≤ C / (N : ℝ) ^ (D + 3) := by
    intro h hh
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hh
    exact hb N ((le_max_left _ _).trans hN) P hP m hm x x'
      (hmember x' hx').1.symm (hmember x' hx').2
  have he : (D + 3) + D = 2 * D + 3 := by omega
  simpa only [OrdinaryTopRelation, he] using hr N ((le_max_right _ _).trans hN)
    ((P x).coeff D : Frequency) T hT hnonzero hd hp

/-- Failure of the actual top relation forces a small number of large compressed blocks. -/
theorem uniform_ordinary_no_relation_count (hW : PolynomialLeadingWeylInput)
    (hR : MonomialDenseReturns) (D : ℕ) (hD : 2 ≤ D)
    (v ρ : ℝ) (hv : 0 < v) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℝ[X], (∀ x, (P x).natDegree ≤ D) →
      ∀ m : Base N → ℂ, (∀ z, ‖m z‖ ≤ 1) → ∀ x : Fin N,
      ¬ OrdinaryTopRelation D Q E N ((P x).coeff D : Frequency) →
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m)
        Finset.univ v x).card : ℝ) < ρ * N := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, ht⟩ := uniform_ordinary_many_blocks_top_relation hW hR D hD v ρ hv hρ
  refine ⟨Q, E, N₀, hQ, hE, hN₀, ?_⟩
  intro N hN P hP m hm x hx
  exact lt_of_not_ge (fun hc => hx (ht N hN P hP m hm x hc))

/-- True masks supported off the top-relation rows have small energy on the same original input. -/
theorem uniform_ordinary_no_relation_operator (hW : PolynomialLeadingWeylInput)
    (hR : MonomialDenseReturns) (D : ℕ) (hD : 2 ≤ D) (s : ℝ) (hs : 0 < s) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℝ[X], (∀ x, (P x).natDegree ≤ D) →
      ∀ m : Base N → ℂ, (∀ z, ‖m z‖ ≤ 1) →
      (∀ x : Fin N, OrdinaryTopRelation D Q E N ((P x).coeff D : Frequency) → ∀ y, m (x, y) = 0) →
      ∀ g : InputBox N → ℂ,
        finiteEnergy (fun z => m z * finiteResponse N (ordinaryOriginalProfile P) g z) ≤
          s ^ 2 * finiteEnergy g := by
  classical
  obtain ⟨ρ, v, hρ, hv, N₁, hN₁, hbudget⟩ := uniform_compressed_block_error_budget s hs
  obtain ⟨Q, E, N₂, hQ, hE, hN₂, hcount⟩ := uniform_ordinary_no_relation_count hW hR D hD v ρ hv hρ
  refine ⟨Q, E, max N₁ N₂, hQ, hE, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN P hP m hm hsupport g
  have hn : 0 < N := hN₁.trans_le ((le_max_left _ _).trans hN)
  have hc : ∀ x ∈ (Finset.univ : Finset (Fin N)),
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m)
        Finset.univ v x).card : ℝ) ≤ ρ * N := by
    intro x _
    by_cases hx : OrdinaryTopRelation D Q E N ((P x).coeff D : Frequency)
    · rw [largeBlockNeighbors_empty_of_zero_row _ _ _ _ (fun y u => by
        simp only [outputMaskedKernel, hsupport x hx y, zero_mul])]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · exact (hcount N ((le_max_right _ _).trans hN) P hP m hm x hx).le
  have hb := masked_original_energy_of_few_large_blocks hn (ordinaryOriginalProfile P) m
    Finset.univ hm (by simp) v ρ hv.le hρ.le hc g
  exact hb.trans (mul_le_mul_of_nonneg_right (hbudget N ((le_max_left _ _).trans hN))
    (finiteEnergy_nonneg g))

end GMZP0
