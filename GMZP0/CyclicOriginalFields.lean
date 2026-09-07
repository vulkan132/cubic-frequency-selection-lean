import GMZP0.RerootedAverage
import Mathlib.Data.ZMod.Basic

/-! Inject the original vertical box into a cyclic group, with exact supported field values. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cyclicRow (N q : ℕ) (y : Fin (N ^ 2)) : ZMod q := (label y : ℕ)

def cyclicField {V : Type*} (N q : ℕ) (F : Base N → V) (fallback : V)
    (x : Fin N) (v : ZMod q) : V :=
  originalFieldExtension N F fallback ((x.val : ℤ) + 1, (v.val : ℤ))

theorem cyclicRow_value {N q : ℕ} (hq : N ^ 2 < q) (y : Fin (N ^ 2)) :
    (cyclicRow N q y).val = label y := by
  have hy : label y < q := by have hi := y.isLt; unfold label; omega
  exact ZMod.val_natCast_of_lt hy

theorem cyclicRow_injective {N q : ℕ} (hq : N ^ 2 < q) : Function.Injective (cyclicRow N q) := by
  intro y z he
  have hv := congrArg ZMod.val he
  rw [cyclicRow_value hq, cyclicRow_value hq] at hv
  apply Fin.ext
  unfold label at hv
  omega

theorem cyclicField_original {V : Type*} {N q : ℕ} (hq : N ^ 2 < q)
    (F : Base N → V) (fallback : V) (x : Fin N) (y : Fin (N ^ 2)) :
    cyclicField N q F fallback x (cyclicRow N q y) = F (x, y) := by
  rw [cyclicField, cyclicRow_value hq]
  simpa only [basePoint, label, Nat.cast_add, Nat.cast_one] using
    originalFieldExtension_base N F fallback (x, y)

theorem cyclicRow_range_iff {N q : ℕ} [NeZero q] (hq : N ^ 2 < q) (v : ZMod q) :
    v ∈ Set.range (cyclicRow N q) ↔ 1 ≤ v.val ∧ v.val ≤ N ^ 2 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [cyclicRow_value hq]
    have hi := y.isLt
    unfold label
    constructor <;> omega
  · rintro ⟨hv0, hvN⟩
    let y : Fin (N ^ 2) := ⟨v.val - 1, by omega⟩
    refine ⟨y, ?_⟩
    have he : label y = v.val := by dsimp [label, y]; omega
    rw [cyclicRow, he, ZMod.natCast_zmod_val]

theorem cyclicField_outside_range {V : Type*} {N q : ℕ} [NeZero q] (hq : N ^ 2 < q)
    (F : Base N → V) (fallback : V) (x : Fin N) (v : ZMod q)
    (hv : v ∉ Set.range (cyclicRow N q)) : cyclicField N q F fallback x v = fallback := by
  have hn : ¬ (1 ≤ v.val ∧ v.val ≤ N ^ 2) := fun h => hv ((cyclicRow_range_iff hq v).2 h)
  apply originalFieldExtension_vertical_outside
  change ¬ (1 ≤ (v.val : ℤ) ∧ (v.val : ℤ) ≤ (N ^ 2 : ℕ))
  exact_mod_cast hn

/-- A shift whose integer representative lies in [0,q) has no cyclic wraparound. -/
theorem cyclicField_shift {V : Type*} {N q : ℕ} [NeZero q]
    (F : Base N → V) (fallback : V) (x : Fin N) (y : Fin (N ^ 2)) (d : ℤ)
    (hd0 : 0 ≤ (y.val : ℤ) + 1 + d) (hdq : (y.val : ℤ) + 1 + d < q) :
    cyclicField N q F fallback x (cyclicRow N q y + (d : ZMod q)) =
      originalFieldExtension N F fallback ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + d) := by
  have he : cyclicRow N q y + (d : ZMod q) = (((y.val : ℤ) + 1 + d : ℤ) : ZMod q) := by
    simp only [cyclicRow, label, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [cyclicField, he, ZMod.val_intCast, Int.emod_eq_of_lt hd0 hdq]

/-- The original weight permits replacing the entire cyclic sum by the original vertical sum. -/
theorem cyclic_original_weighted_sum {N q : ℕ} [NeZero q] (hq : N ^ 2 < q)
    (σ : Base N → ℝ) (x : Fin N) (A : ZMod q → ℝ) :
    (∑ v : ZMod q, cyclicField N q σ 0 x v * A v) =
      ∑ y : Fin (N ^ 2), σ (x, y) * A (cyclicRow N q y) := by
  symm
  apply Fintype.sum_of_injective (cyclicRow N q) (cyclicRow_injective hq)
  · intro v hv
    rw [cyclicField_outside_range hq σ 0 x v hv, zero_mul]
  · intro y
    rw [cyclicField_original hq]

end GMZP0
