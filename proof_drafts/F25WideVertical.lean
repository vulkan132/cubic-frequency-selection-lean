import GMZP0.IntegerBlockFormula
import GMZP0.OriginalBlockSchur

/-! A finite vertical enlargement contains every original block target, without a safe-source assumption. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- A truncated exponential sum cannot in general be bounded by the complete sum's modulus. -/
theorem truncated_sum_modulus_obstruction :
    ∃ a : Bool → ℂ, (∀ b, ‖a b‖ = 1) ∧ ‖∑ b : Bool, a b‖ < ‖a true‖ := by
  refine ⟨fun b => if b then 1 else -1, ?_, ?_⟩
  · intro b
    cases b <;> norm_num
  · norm_num

abbrev WideVertical (N : ℕ) := Fin (3 * N ^ 2)

/-- Enlarged input coordinates range from 1-N^2 through 2*N^2. -/
def wideVerticalCoordinate {N : ℕ} (v : WideVertical N) : ℤ :=
  (v.val : ℤ) + 1 - (N ^ 2 : ℕ)

/-- Actual original vertical points embed without changing their integer coordinates. -/
def wideVerticalEmbed {N : ℕ} (y : Fin (N ^ 2)) : WideVertical N :=
  ⟨y.val + N ^ 2, by have hy := y.isLt; omega⟩

/-- The enlarged coordinate representation is injective. -/
theorem wideVerticalCoordinate_injective {N : ℕ} : Function.Injective (@wideVerticalCoordinate N) := by
  intro v w h
  apply Fin.ext
  simp only [wideVerticalCoordinate] at h
  omega

/-- The original embedding has exactly its original one-based coordinate. -/
theorem wideVerticalEmbed_coordinate {N : ℕ} (y : Fin (N ^ 2)) :
    wideVerticalCoordinate (wideVerticalEmbed y) = (label y : ℤ) := by
  simp only [wideVerticalCoordinate, wideVerticalEmbed, label, Nat.cast_add, Nat.cast_one]
  ring

/-- The original vertical embedding is injective. -/
theorem wideVerticalEmbed_injective {N : ℕ} : Function.Injective (@wideVerticalEmbed N) := by
  intro y v h
  have hval := congrArg Fin.val h
  apply Fin.ext
  simp only [wideVerticalEmbed] at hval
  omega

/-- Convert any coordinate in the enlarged interval to its exact finite index. -/
def wideVerticalIndex (N : ℕ) (u : ℤ)
    (hu0 : 1 - (N ^ 2 : ℕ) ≤ u) (hu1 : u ≤ 2 * (N ^ 2 : ℕ)) : WideVertical N :=
  ⟨(u - 1 + (N ^ 2 : ℕ)).toNat, by omega⟩

/-- The conversion back to an enlarged coordinate is exact. -/
theorem wideVerticalIndex_coordinate (N : ℕ) (u : ℤ)
    (hu0 : 1 - (N ^ 2 : ℕ) ≤ u) (hu1 : u ≤ 2 * (N ^ 2 : ℕ)) :
    wideVerticalCoordinate (wideVerticalIndex N u hu0 hu1) = u := by
  simp only [wideVerticalCoordinate, wideVerticalIndex]
  omega

/-- Every pair of original labels has its parabola target in the enlarged interval. -/
theorem wide_parabola_target_bounds {N : ℕ} (y : Fin (N ^ 2)) (r s : Fin N) :
    1 - (N ^ 2 : ℕ) ≤ (label y : ℤ) + (label r : ℤ) ^ 2 - (label s : ℤ) ^ 2 ∧
      (label y : ℤ) + (label r : ℤ) ^ 2 - (label s : ℤ) ^ 2 ≤ 2 * (N ^ 2 : ℕ) := by
  have hy := integer_label_bounds y
  have hr : (label r : ℤ) ^ 2 ≤ (N ^ 2 : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_left (Nat.succ_le_of_lt r.isLt) 2
  have hs : (label s : ℤ) ^ 2 ≤ (N ^ 2 : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_left (Nat.succ_le_of_lt s.isLt) 2
  constructor <;> nlinarith [sq_nonneg (label r : ℤ), sq_nonneg (label s : ℤ)]

/-- A target for every pair of original labels, including rows near the original boundary. -/
def wideParabolaTarget {N : ℕ} (y : Fin (N ^ 2)) (r s : Fin N) : WideVertical N :=
  wideVerticalIndex N ((label y : ℤ) + (label r : ℤ) ^ 2 - (label s : ℤ) ^ 2)
    (wide_parabola_target_bounds y r s).1 (wide_parabola_target_bounds y r s).2

/-- Every enlarged target retains the exact original parabola coordinate. -/
theorem wideParabolaTarget_coordinate {N : ℕ} (y : Fin (N ^ 2)) (r s : Fin N) :
    wideVerticalCoordinate (wideParabolaTarget y r s) =
      (label y : ℤ) + (label r : ℤ) ^ 2 - (label s : ℤ) ^ 2 :=
  wideVerticalIndex_coordinate ..

/-- Valid original block labels have targets in the enlarged input for every original source. -/
def wideBlockTarget {N : ℕ} (y : Fin (N ^ 2)) (h : ℤ) (r : blockFinLabels N h) : WideVertical N :=
  wideParabolaTarget y r.val (shiftedBlockLabel h r)

/-- The enlarged target is exactly y+2hr-h^2, with no SafeVertical premise. -/
theorem wideBlockTarget_coordinate {N : ℕ} (y : Fin (N ^ 2)) (h : ℤ) (r : blockFinLabels N h) :
    wideVerticalCoordinate (wideBlockTarget y h r) =
      (label y : ℤ) + 2 * h * (label r.val : ℤ) - h ^ 2 := by
  rw [wideBlockTarget, wideParabolaTarget_coordinate, shiftedBlockLabel_value]
  ring

/-- Nonzero horizontal displacement makes the complete label-to-target map injective. -/
theorem wideBlockTarget_injective {N : ℕ} (y : Fin (N ^ 2)) (h : ℤ) (hh : h ≠ 0) :
    Function.Injective (wideBlockTarget y h) := by
  intro r s he
  have hc := congrArg wideVerticalCoordinate he
  simp only [wideBlockTarget_coordinate] at hc
  have hp : (2 * h) * ((label r.val : ℤ) - (label s.val : ℤ)) = 0 := by nlinarith only [hc]
  have hl := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (by decide) hh)
  apply Subtype.ext
  apply Fin.ext
  simp only [label, Nat.cast_add, Nat.cast_one] at hl
  omega

/-- Equality with an embedded original target is equivalent to the actual original collision. -/
theorem wideBlockTarget_original_collision {N : ℕ} (x x' : Fin N) (y v : Fin (N ^ 2))
    (r : blockFinLabels N (horizontalGap x x')) :
    wideBlockTarget y (horizontalGap x x') r = wideVerticalEmbed v ↔
      endpointIndex (x, y) r.val = endpointIndex (x', v) (shiftedBlockLabel (horizontalGap x x') r) := by
  rw [← wideVerticalCoordinate_injective.eq_iff, wideBlockTarget_coordinate, wideVerticalEmbed_coordinate,
    endpointIndex_collision_iff]
  rw [shiftedBlockLabel_value]
  simp only [basePoint, add_sub_add_right_eq_sub, horizontalGap,
    label, Nat.cast_add, Nat.cast_one, true_and]
  exact eq_comm

end GMZP0
