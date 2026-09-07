import GMZP0.PairCollision
import GMZP0.FiniteUnionMean

/-! The complete collision bound for all sixteen actual cyclic cube vertices. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cubeVertexEnumeration : Fin 16 ≃ (Fin 4 → Bool) := Fintype.equivOfCardEq (by decide)

abbrev AscendingCubeLabelPairs := {ij : Fin 16 × Fin 16 // ij.1 < ij.2}

theorem card_ascendingCubeLabelPairs : Fintype.card AscendingCubeLabelPairs = 120 := by
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
  norm_num [Nat.choose_two_right]

theorem cube_collision_probability {q ℓ : ℕ} [Fact q.Prime] (hℓ : 2 * ℓ < q)
    (h : ℤ) (hs : ((2 * h : ℤ) : ZMod q) ≠ 0) (Y : ZMod q) :
    realUniformMean (fun u : CubeShiftPairs ℓ =>
      if ¬ Function.Injective (cyclicCubeVertex q ℓ h Y u) then 1 else 0) ≤
        120 / (2 * (ℓ : ℝ) + 1) := by
  classical
  let P (u : CubeShiftPairs ℓ) := ¬ Function.Injective (cyclicCubeVertex q ℓ h Y u)
  let Q (u : CubeShiftPairs ℓ) (ij : AscendingCubeLabelPairs) :=
    cyclicCubeVertex q ℓ h Y u (cubeVertexEnumeration ij.val.1) =
      cyclicCubeVertex q ℓ h Y u (cubeVertexEnumeration ij.val.2)
  have hcover : ∀ u, P u → ∃ ij, Q u ij := by
    intro u hu
    obtain ⟨ω, ω', he, hne⟩ := Function.not_injective_iff.mp hu
    let i := cubeVertexEnumeration.symm ω
    let j := cubeVertexEnumeration.symm ω'
    have hij : i ≠ j := fun hh => hne (cubeVertexEnumeration.symm.injective hh)
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨⟨(i, j), hij⟩, ?_⟩
      simpa only [Q, i, j, Equiv.apply_symm_apply] using he
    · refine ⟨⟨(j, i), hji⟩, ?_⟩
      simpa only [Q, i, j, Equiv.apply_symm_apply] using he.symm
  have hu := uniform_event_union_le P Q hcover
  have hp (ij : AscendingCubeLabelPairs) :
      realUniformMean (fun u => if Q u ij then 1 else 0) ≤ 1 / (2 * (ℓ : ℝ) + 1) := by
    apply cube_pair_collision_probability hℓ h hs Y
    exact fun he => (ne_of_lt ij.property) (cubeVertexEnumeration.injective he)
  have hsums := Finset.sum_le_sum (fun ij (_ : ij ∈ (Finset.univ : Finset AscendingCubeLabelPairs)) => hp ij)
  have hc : (∑ _ : AscendingCubeLabelPairs, (1 : ℝ) / (2 * (ℓ : ℝ) + 1)) =
      120 / (2 * (ℓ : ℝ) + 1) := by
    simp only [Finset.sum_const, Finset.card_univ, card_ascendingCubeLabelPairs, nsmul_eq_mul]
    ring
  exact hu.trans (hsums.trans_eq hc)

theorem positive_cube_collision_probability {N q ℓ : ℕ} [Fact q.Prime]
    (hℓ : 2 * ℓ < q) (hq : 2 * N < q) (h : Fin N) (Y : ZMod q) :
    realUniformMean (fun u : CubeShiftPairs ℓ =>
      if ¬ Function.Injective (cyclicCubeVertex q ℓ (label h) Y u) then 1 else 0) ≤
        120 / (2 * (ℓ : ℝ) + 1) :=
  cube_collision_probability hℓ (label h) (positive_cube_step_ne_zero hq h) Y

end GMZP0
