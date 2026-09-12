import GMZP0.WideBlock
import GMZP0.LagReindexing

/-! Complete widened Gram phases at every original source, without a safe-window restriction. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- Two complete block labels share a widened target exactly at displacement 2h(r-s). -/
theorem wideBlockTarget_shared_iff {N : ℕ} (y t : Fin (N ^ 2)) (h : ℤ)
    (r s : blockFinLabels N h) :
    wideBlockTarget y h r = wideBlockTarget t h s ↔
      (label t : ℤ) = (label y : ℤ) + 2 * h * ((label r.val : ℤ) - (label s.val : ℤ)) := by
  rw [← wideVerticalCoordinate_injective.eq_iff, wideBlockTarget_coordinate, wideBlockTarget_coordinate]
  constructor <;> intro he <;> nlinarith only [he]

/-- Widened Gram entries contain all pairs of original block labels sharing a target. -/
theorem wideHorizontalKernel_gram_labels {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y t : Fin (N ^ 2)) :
    gramKernel (wideHorizontalKernel P x x') y t =
      ∑ r : blockFinLabels N (horizontalGap x x'), ∑ s : blockFinLabels N (horizontalGap x x'),
        if wideBlockTarget y (horizontalGap x x') r = wideBlockTarget t (horizontalGap x x') s then
          wideBlockCoefficient P x x' y r * conj (wideBlockCoefficient P x x' t s) else 0 := by
  classical
  simp only [gramKernel, wideHorizontalKernel, map_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [apply_ite, map_zero, ite_mul, zero_mul, mul_zero]
  by_cases ht : wideBlockTarget y (horizontalGap x x') r = wideBlockTarget t (horizontalGap x x') s <;>
    simp [ht, eq_comm]

/-- The shared-target coefficient product has the exact original four-factor circle phase. -/
theorem wideBlockCoefficient_shared_product {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y t : Fin (N ^ 2)) (r s : blockFinLabels N (horizontalGap x x'))
    (he : wideBlockTarget y (horizontalGap x x') r = wideBlockTarget t (horizontalGap x x') s) :
    wideBlockCoefficient P x x' y r * conj (wideBlockCoefficient P x x' t s) =
      circleCharacter (doublePhaseCoefficient (P x (label y)) (P x (label t))
        (P x' (wideVerticalCoordinate (wideBlockTarget y (horizontalGap x x') r)))
        (horizontalGap x x') ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val)) / (N : ℂ) ^ 4 := by
  simp only [wideBlockCoefficient, ← he, cubicPhase_integer, shiftedBlockLabel_value,
    map_div₀, map_pow, map_natCast]
  rw [div_mul_div_comm]
  have hp := double_phase_character (P x (label y)) (P x (label t))
    (P x' (wideVerticalCoordinate (wideBlockTarget y (horizontalGap x x') r)))
    (horizontalGap x x') ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val)
  have hadd : (label s.val : ℤ) + ((label r.val : ℤ) - (label s.val : ℤ)) = (label r.val : ℤ) := by ring
  rw [hadd] at hp
  rw [hp]
  congr 1
  ring

/-- The manuscript's total double phase, evaluated using the supplied full-integer profile. -/
def wideDoublePhase {N : ℕ} (P : Fin N → ℤ → Frequency) (x x' : Fin N) (y k r : ℤ) : Frequency :=
  doublePhaseCoefficient (P x y) (P x (y + 2 * horizontalGap x x' * k))
    (P x' (y + 2 * horizontalGap x x' * (r + k) - horizontalGap x x' ^ 2))
    (horizontalGap x x') k r

/-- At a shared target the coefficient product has exactly the paper's y,h,k,r formula. -/
theorem wideBlockCoefficient_double_phase {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y t : Fin (N ^ 2)) (r s : blockFinLabels N (horizontalGap x x'))
    (he : wideBlockTarget y (horizontalGap x x') r = wideBlockTarget t (horizontalGap x x') s) :
    wideBlockCoefficient P x x' y r * conj (wideBlockCoefficient P x x' t s) =
      circleCharacter (wideDoublePhase P x x' (label y)
        ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val)) / (N : ℂ) ^ 4 := by
  rw [wideBlockCoefficient_shared_product P x x' y t r s he]
  have ht := (wideBlockTarget_shared_iff y t (horizontalGap x x') r s).1 he
  simp only [wideDoublePhase, ht, wideBlockTarget_coordinate, add_sub_cancel]

/-- The exact complete pair formula has the original N^(-4) normalization. -/
theorem wideHorizontalKernel_gram_phase_pairs {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y t : Fin (N ^ 2)) :
    gramKernel (wideHorizontalKernel P x x') y t =
      (∑ r : blockFinLabels N (horizontalGap x x'), ∑ s : blockFinLabels N (horizontalGap x x'),
        if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' *
            ((label r.val : ℤ) - (label s.val : ℤ)) then
          circleCharacter (wideDoublePhase P x x' (label y)
            ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val)) else 0) / (N : ℂ) ^ 4 := by
  classical
  rw [wideHorizontalKernel_gram_labels]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases he : wideBlockTarget y (horizontalGap x x') r = wideBlockTarget t (horizontalGap x x') s
  · have ht := (wideBlockTarget_shared_iff y t (horizontalGap x x') r s).1 he
    simp only [if_pos he, if_pos ht, wideBlockCoefficient_double_phase P x x' y t r s he, div_eq_mul_inv]
  · have ht := mt (wideBlockTarget_shared_iff y t (horizontalGap x x') r s).2 he
    simp only [if_neg he, if_neg ht, zero_mul]

/-- The complete affine pair reindexing also applies to complex-valued phase sums. -/
theorem complete_blockFinLabels_pair_sum {M : Type*} [AddCommMonoid M]
    (N : ℕ) (h : ℤ) (F : ℤ → ℤ → M) :
    (∑ r : blockFinLabels N h, ∑ s : blockFinLabels N h,
      F ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k, F k r := by
  calc
    _ = ∑ r : blockFinLabels N h, ∑ s ∈ blockLabels N h, F ((label r.val : ℤ) - s) s := by
      apply Finset.sum_congr rfl
      intro r _
      exact sum_blockFinLabels N h (fun s => F ((label r.val : ℤ) - s) s)
    _ = ∑ r ∈ blockLabels N h, ∑ s ∈ blockLabels N h, F (r - s) s :=
      sum_blockFinLabels N h (fun r => ∑ s ∈ blockLabels N h, F (r - s) s)
    _ = _ := integer_label_pair_sum N h F

/-- Every widened Gram entry is a complete lag sum, at every original source row. -/
theorem wideHorizontalKernel_gram_lags {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y t : Fin (N ^ 2)) :
    gramKernel (wideHorizontalKernel P x x') y t =
      (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' * k then
          ∑ r ∈ lagLabels N (horizontalGap x x') k, circleCharacter (wideDoublePhase P x x' (label y) k r)
        else 0) / (N : ℂ) ^ 4 := by
  classical
  rw [wideHorizontalKernel_gram_phase_pairs,
    complete_blockFinLabels_pair_sum N (horizontalGap x x')
      (fun k r => if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' * k then
        circleCharacter (wideDoublePhase P x x' (label y) k r) else 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

end GMZP0
