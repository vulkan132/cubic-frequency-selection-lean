import GMZP0.LagGeometry

/-! Canonical original indices for every valid single-block label from a safe source row. -/

noncomputable section
namespace GMZP0

def oneBasedIndex (n : ℕ) (u : ℤ) (hu0 : 1 ≤ u) (hun : u ≤ n) : Fin n :=
  ⟨(u - 1).toNat, by omega⟩

theorem oneBasedIndex_label (n : ℕ) (u : ℤ) (hu0 : 1 ≤ u) (hun : u ≤ n) :
    (label (oneBasedIndex n u hu0 hun) : ℤ) = u := by
  simp only [oneBasedIndex, label, Nat.cast_add, Nat.cast_one]
  omega

def blockFinLabels (N : ℕ) (h : ℤ) : Finset (Fin N) :=
  Finset.univ.filter fun r => 1 ≤ (label r : ℤ) - h ∧ (label r : ℤ) - h ≤ N

def shiftedBlockLabel {N : ℕ} (h : ℤ) (r : blockFinLabels N h) : Fin N :=
  oneBasedIndex N ((label r.val : ℤ) - h) (Finset.mem_filter.mp r.property).2.1
    (Finset.mem_filter.mp r.property).2.2

theorem shiftedBlockLabel_value {N : ℕ} (h : ℤ) (r : blockFinLabels N h) :
    (label (shiftedBlockLabel h r) : ℤ) = (label r.val : ℤ) - h := by
  exact oneBasedIndex_label _ _ _ _

def blockTarget {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (h : ℤ) (hh : |h| ≤ H)
    (hHN : H ≤ N) (r : Fin N) : Fin (N ^ 2) := by
  have ht := safe_parabola_target N H ((y.val : ℤ) + 1) h (label r) hy (Nat.cast_nonneg _)
    (by exact_mod_cast hHN) hh (Nat.cast_nonneg _) (integer_label_bounds r).2
  exact oneBasedIndex (N ^ 2) ((y.val : ℤ) + 1 + 2 * h * (label r : ℤ) - h ^ 2)
    ht.1 (by exact_mod_cast ht.2)

theorem blockTarget_coordinate {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (h : ℤ) (hh : |h| ≤ H)
    (hHN : H ≤ N) (r : Fin N) :
    (label (blockTarget H y hy h hh hHN r) : ℤ) =
      (y.val : ℤ) + 1 + 2 * h * (label r : ℤ) - h ^ 2 := by
  unfold blockTarget
  exact oneBasedIndex_label _ _ _ _

theorem blockTarget_injective {N : ℕ} (H : ℕ) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (h : ℤ) (hh : |h| ≤ H)
    (hHN : H ≤ N) (hne : h ≠ 0) : Function.Injective (blockTarget H y hy h hh hHN) := by
  intro r s he
  have hp := congrArg (fun v : Fin (N ^ 2) => (label v : ℤ)) he
  rw [blockTarget_coordinate, blockTarget_coordinate] at hp
  have hzero : (2 * h) * ((label r : ℤ) - (label s : ℤ)) = 0 := by nlinarith only [hp]
  have hl := (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by decide) hne)
  apply Fin.ext
  simp only [label, Nat.cast_add, Nat.cast_one] at hl
  omega

/-- The canonical target and shifted label really share the original parabola endpoint. -/
theorem blockTarget_collision {N : ℕ} (H : ℕ) (x x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r : blockFinLabels N (horizontalGap x x')) :
    endpointIndex (x, y) r.val =
      endpointIndex (x', blockTarget H y hy (horizontalGap x x') hh hHN r.val)
        (shiftedBlockLabel (horizontalGap x x') r) := by
  rw [endpointIndex_collision_iff]
  constructor
  · simpa only [basePoint, add_sub_add_right_eq_sub, horizontalGap] using
      shiftedBlockLabel_value (horizontalGap x x') r
  · simpa only [basePoint, label, Nat.cast_add, Nat.cast_one,
      add_sub_add_right_eq_sub, horizontalGap] using
      blockTarget_coordinate H y hy (horizontalGap x x') hh hHN r.val

/-- Every original collision at a safe source appears in this canonical label-target family. -/
theorem collision_in_blockTargets {N : ℕ} (H : ℕ) (x x' : Fin N) (y v : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r s : Fin N) (he : endpointIndex (x, y) r = endpointIndex (x', v) s) :
    r ∈ blockFinLabels N (horizontalGap x x') ∧
      blockTarget H y hy (horizontalGap x x') hh hHN r = v := by
  have hg := (endpointIndex_collision_iff (x, y) (x', v) r s).1 he
  simp only [basePoint, add_sub_add_right_eq_sub] at hg
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hs := integer_label_bounds s
    change 1 ≤ (label r : ℤ) - horizontalGap x x' ∧ (label r : ℤ) - horizontalGap x x' ≤ N
    simpa only [horizontalGap, ← hg.1] using hs
  · have hv := blockTarget_coordinate H y hy (horizontalGap x x') hh hHN r
    have heq : (label (blockTarget H y hy (horizontalGap x x') hh hHN r) : ℤ) = (v.val : ℤ) + 1 :=
      hv.trans hg.2.symm
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at heq
    omega

end GMZP0
