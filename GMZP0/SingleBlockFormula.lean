import GMZP0.BlockTargets
import GMZP0.CircleCharacter

/-! Exact single-label horizontal block formula at a safe original source. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem blockFinLabels_membership (N : ℕ) (h : ℤ) (r : Fin N) :
    r ∈ blockFinLabels N h ↔ (label r : ℤ) ∈ blockLabels N h := by
  simp only [blockFinLabels, Finset.mem_filter, Finset.mem_univ, true_and, mem_blockLabels_iff]
  exact ⟨fun hr => ⟨integer_label_bounds r, hr⟩, fun hr => hr.2⟩

def blockCoefficient {N : ℕ} (H : ℕ) (p : Base N → Frequency) (x x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r : blockFinLabels N (horizontalGap x x')) : ℂ :=
  cubicPhase (p (x, y)) r.val *
    conj (cubicPhase (p (x', blockTarget H y hy (horizontalGap x x') hh hHN r.val))
      (shiftedBlockLabel (horizontalGap x x') r)) / (N : ℂ) ^ 2

/-- Every row entry is the sum of precisely its valid original label contributions. -/
theorem horizontalKernel_label_formula {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (v : Fin (N ^ 2)) :
    horizontalKernel N p x x' y v =
      ∑ r : blockFinLabels N (horizontalGap x x'),
        if blockTarget H y hy (horizontalGap x x') hh hHN r.val = v then
          blockCoefficient H p x x' y hy hh hHN r else 0 := by
  classical
  let T : blockFinLabels N (horizontalGap x x') → Fin (N ^ 2) :=
    fun r => blockTarget H y hy (horizontalGap x x') hh hHN r.val
  let W := blockCoefficient H p x x' y hy hh hHN
  change horizontalKernel N p x x' y v = ∑ r, if T r = v then W r else 0
  have hinj : Function.Injective T := by
    intro r s he
    exact Subtype.ext (blockTarget_injective H y hy (horizontalGap x x') hh hHN
      (horizontalGap_ne_zero x x' hx) he)
  have hkernel : ∀ r, horizontalKernel N p x x' y (T r) = W r := by
    intro r
    exact horizontalKernel_of_collision p x x' hx y (T r) r.val
      (shiftedBlockLabel (horizontalGap x x') r) (blockTarget_collision H x x' y hy hh hHN r)
  by_cases hex : ∃ r, T r = v
  · obtain ⟨r, hr⟩ := hex
    have hiff : ∀ s, T s = v ↔ s = r := by
      intro s
      exact ⟨fun hs => hinj (hs.trans hr.symm), fun hs => hs ▸ hr⟩
    simp_rw [hiff]
    rw [Fintype.sum_ite_eq', ← hr]
    exact hkernel r
  · have hn : ∀ r s : Fin N, endpointIndex (x, y) r ≠ endpointIndex (x', v) s := by
      intro r s he
      obtain ⟨hr, hv⟩ := collision_in_blockTargets H x x' y v hy hh hHN r s he
      exact hex ⟨⟨r, hr⟩, hv⟩
    rw [horizontalKernel_no_collision p x x' y v hn]
    symm
    apply Finset.sum_eq_zero
    intro r _
    exact if_neg (fun he => hex ⟨r, he⟩)

/-- The actual finite horizontal operator is a single complete sum over I_h labels. -/
theorem horizontalBlock_action_labels {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (g : Fin (N ^ 2) → ℂ) :
    kernelAction (horizontalKernel N p x x') g y =
      ∑ r : blockFinLabels N (horizontalGap x x'),
        blockCoefficient H p x x' y hy hh hHN r *
          g (blockTarget H y hy (horizontalGap x x') hh hHN r.val) := by
  simp only [kernelAction, horizontalKernel_label_formula H p x x' hx y hy hh hHN,
    Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq]

/-- The single-label phase is exactly p_x(y)r³-p_(x+h)(y+2hr-h²)(r-h)³ on the circle. -/
theorem blockCoefficient_character {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r : blockFinLabels N (horizontalGap x x')) :
    blockCoefficient H p x x' y hy hh hHN r =
      circleCharacter ((label r.val : ℤ) ^ 3 • p (x, y) -
        ((label r.val : ℤ) - horizontalGap x x') ^ 3 •
          p (x', blockTarget H y hy (horizontalGap x x') hh hHN r.val)) / (N : ℂ) ^ 2 := by
  simp only [blockCoefficient, cubicPhase_integer, integerCubicPhase,
    shiftedBlockLabel_value, circleCharacter_sub]

end GMZP0
