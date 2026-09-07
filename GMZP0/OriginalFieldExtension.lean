import GMZP0.LagSources

/-! Total integer-coordinate expressions that agree exactly with every original field evaluation. -/

noncomputable section
namespace GMZP0

def originalFieldExtension {V : Type*} (N : ℕ) (F : Base N → V) (fallback : V) (w : ℤ × ℤ) : V :=
  if hx : 1 ≤ w.1 ∧ w.1 ≤ N then
    if hy : 1 ≤ w.2 ∧ w.2 ≤ (N ^ 2 : ℕ) then
      F (oneBasedIndex N w.1 hx.1 hx.2, oneBasedIndex (N ^ 2) w.2 hy.1 hy.2)
    else fallback
  else fallback

theorem originalFieldExtension_vertical_outside {V : Type*} (N : ℕ)
    (F : Base N → V) (fallback : V) (w : ℤ × ℤ)
    (hy : ¬ (1 ≤ w.2 ∧ w.2 ≤ (N ^ 2 : ℕ))) :
    originalFieldExtension N F fallback w = fallback := by
  simp only [originalFieldExtension, dif_neg hy, dite_eq_ite, ite_self]

theorem originalFieldExtension_base {V : Type*} (N : ℕ) (F : Base N → V) (fallback : V) (z : Base N) :
    originalFieldExtension N F fallback (basePoint z) = F z := by
  have he : basePoint z = ((label z.1 : ℤ), (label z.2 : ℤ)) := by
    simp only [basePoint, label, Nat.cast_add, Nat.cast_one]
  rw [he]
  simp only [originalFieldExtension, integer_label_bounds, and_self, dite_true, oneBasedIndex_of_label]

theorem originalFieldExtension_lagSource {V : Type*} {N : ℕ} (H : ℕ)
    (F : Base N → V) (fallback : V) (x : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (r s : Fin N) :
    originalFieldExtension N F fallback
      ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * ((label r : ℤ) - (label s : ℤ))) =
      F (x, lagSource H y hy h hh r s) := by
  have he : basePoint (x, lagSource H y hy h hh r s) =
      ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * ((label r : ℤ) - (label s : ℤ))) := by
    apply Prod.ext
    · rfl
    · simpa only [basePoint, label, Nat.cast_add, Nat.cast_one] using
        lagSource_coordinate H y hy h hh r s
  rw [← he, originalFieldExtension_base]

theorem originalFieldExtension_blockTarget {V : Type*} {N : ℕ} (H : ℕ)
    (F : Base N → V) (fallback : V) (x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h : ℤ) (hh : |h| ≤ H) (hHN : H ≤ N) (r : Fin N) :
    originalFieldExtension N F fallback
      ((x'.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * (label r : ℤ) - h ^ 2) =
      F (x', blockTarget H y hy h hh hHN r) := by
  have he : basePoint (x', blockTarget H y hy h hh hHN r) =
      ((x'.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * (label r : ℤ) - h ^ 2) := by
    apply Prod.ext
    · rfl
    · simpa only [basePoint, label, Nat.cast_add, Nat.cast_one] using
        blockTarget_coordinate H y hy h hh hHN r
  rw [← he, originalFieldExtension_base]

end GMZP0
