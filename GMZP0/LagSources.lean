import GMZP0.IntegerBlockFormula

/-! The second source of every pair of original labels, with its actual finite index. -/

noncomputable section
namespace GMZP0

theorem label_difference_bound {N : ℕ} (r s : Fin N) :
    |(label r : ℤ) - (label s : ℤ)| < N := by
  have hr := integer_label_bounds r
  have hs := integer_label_bounds s
  exact abs_lt.mpr ⟨by omega, by omega⟩

def lagSource {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (r s : Fin N) : Fin (N ^ 2) := by
  have ht := safe_lag_target N H ((y.val : ℤ) + 1) h ((label r : ℤ) - (label s : ℤ))
    hy (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh (le_of_lt (label_difference_bound r s))
  exact oneBasedIndex (N ^ 2) ((y.val : ℤ) + 1 + 2 * h * ((label r : ℤ) - (label s : ℤ)))
    ht.1 (by exact_mod_cast ht.2)

theorem lagSource_coordinate {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (r s : Fin N) :
    (label (lagSource H y hy h hh r s) : ℤ) =
      (y.val : ℤ) + 1 + 2 * h * ((label r : ℤ) - (label s : ℤ)) := by
  unfold lagSource
  exact oneBasedIndex_label _ _ _ _

theorem lagSource_injective {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (hne : h ≠ 0) (r : Fin N) :
    Function.Injective (lagSource H y hy h hh r) := by
  intro s t he
  have hp := congrArg (fun v : Fin (N ^ 2) => (label v : ℤ)) he
  rw [lagSource_coordinate, lagSource_coordinate] at hp
  have hz : (2 * h) * ((label s : ℤ) - (label t : ℤ)) = 0 := by nlinarith only [hp]
  have hl := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by decide) hne)
  apply Fin.ext
  simp only [label, Nat.cast_add, Nat.cast_one] at hl
  omega

theorem lagSource_self {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (r : Fin N) : lagSource H y hy h hh r r = y := by
  have he := lagSource_coordinate H y hy h hh r r
  apply Fin.ext
  simp only [label, Nat.cast_add, Nat.cast_one, sub_self, mul_zero, add_zero] at he
  omega

theorem lagSource_eq_self_iff {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (hne : h ≠ 0) (r s : Fin N) :
    lagSource H y hy h hh r s = y ↔ s = r := by
  constructor
  · intro he
    exact lagSource_injective H y hy h hh hne r
      (he.trans (lagSource_self H y hy h hh r).symm)
  · intro he
    subst s
    exact lagSource_self H y hy h hh r

/-- Every second valid label reaches the same original target from the canonical lag source. -/
theorem lagSource_collision {N : ℕ} (H : ℕ) (x x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r : Fin N) (s : blockFinLabels N (horizontalGap x x')) :
    endpointIndex (x, lagSource H y hy (horizontalGap x x') hh r s.val) s.val =
      endpointIndex (x', blockTarget H y hy (horizontalGap x x') hh hHN r)
        (shiftedBlockLabel (horizontalGap x x') s) := by
  rw [endpointIndex_collision_iff]
  constructor
  · simpa only [basePoint, add_sub_add_right_eq_sub, horizontalGap] using
      shiftedBlockLabel_value (horizontalGap x x') s
  · have hv := blockTarget_coordinate H y hy (horizontalGap x x') hh hHN r
    have ht := lagSource_coordinate H y hy (horizontalGap x x') hh r s.val
    simp only [basePoint, add_sub_add_right_eq_sub]
    simp only [label, Nat.cast_add, Nat.cast_one] at hv ht ⊢
    unfold horizontalGap at hv ht ⊢
    nlinarith only [hv, ht]

/-- Conversely, every original collision at that target comes from a valid second label. -/
theorem collision_in_lagSources {N : ℕ} (H : ℕ) (x x' : Fin N) (y t : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r : Fin N) (s u : Fin N)
    (he : endpointIndex (x, t) s =
      endpointIndex (x', blockTarget H y hy (horizontalGap x x') hh hHN r) u) :
    s ∈ blockFinLabels N (horizontalGap x x') ∧
      lagSource H y hy (horizontalGap x x') hh r s = t := by
  have hg := (endpointIndex_collision_iff _ _ s u).1 he
  simp only [basePoint, add_sub_add_right_eq_sub] at hg
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hu := integer_label_bounds u
    change 1 ≤ (label s : ℤ) - horizontalGap x x' ∧ (label s : ℤ) - horizontalGap x x' ≤ N
    simpa only [horizontalGap, ← hg.1] using hu
  · have hv := blockTarget_coordinate H y hy (horizontalGap x x') hh hHN r
    have ht := lagSource_coordinate H y hy (horizontalGap x x') hh r s
    have hv' : (label (blockTarget H y hy (horizontalGap x x') hh hHN r) : ℤ) =
        (t.val : ℤ) + 1 + 2 * horizontalGap x x' * (label s : ℤ) - horizontalGap x x' ^ 2 := hg.2
    have heq : (label (lagSource H y hy (horizontalGap x x') hh r s) : ℤ) = (t.val : ℤ) + 1 := by
      nlinarith only [hv, hv', ht]
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at heq
    omega

end GMZP0
