import GMZP0.FiniteOperator
import Mathlib.Data.ZMod.Basic

/-! A zero-based cyclic coordinate for the original input, with exact recovery.
The original integer y-coordinate remains the cyclic index plus one. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

def finiteCyclicIndex (M q : ℕ) (y : Fin M) : ZMod q := y.val

theorem finiteCyclicIndex_val {M q : ℕ} (hMq : M ≤ q) (y : Fin M) :
    (finiteCyclicIndex M q y).val = y.val :=
  ZMod.val_natCast_of_lt (lt_of_lt_of_le y.isLt hMq)

theorem finiteCyclicIndex_injective {M q : ℕ} (hMq : M ≤ q) :
    Function.Injective (finiteCyclicIndex M q) := by
  intro y z h
  apply Fin.ext
  simpa only [finiteCyclicIndex_val hMq] using congrArg ZMod.val h

def cyclicZeroExtend (M q : ℕ) (f : Fin M → ℂ) (Y : ZMod q) : ℂ :=
  if h : Y.val < M then f ⟨Y.val, h⟩ else 0

theorem cyclicZeroExtend_original {M q : ℕ} (hMq : M ≤ q)
    (f : Fin M → ℂ) (y : Fin M) :
    cyclicZeroExtend M q f (finiteCyclicIndex M q y) = f y := by
  simp [cyclicZeroExtend, finiteCyclicIndex_val hMq, y.isLt]

theorem cyclicZeroExtend_outside {M q : ℕ} [NeZero q] (f : Fin M → ℂ) (Y : ZMod q)
    (hY : Y ∉ Set.range (finiteCyclicIndex M q)) : cyclicZeroExtend M q f Y = 0 := by
  have hn : ¬ Y.val < M := by
    intro h
    apply hY
    exact ⟨⟨Y.val, h⟩, ZMod.natCast_zmod_val Y⟩
  simp [cyclicZeroExtend, hn]

/-- Zero extension preserves counting energy exactly, not just up to the cyclic modulus. -/
theorem cyclicZeroExtend_energy {M q : ℕ} [NeZero q] (hMq : M ≤ q) (f : Fin M → ℂ) :
    (∑ Y : ZMod q, ‖cyclicZeroExtend M q f Y‖ ^ 2) = ∑ y, ‖f y‖ ^ 2 := by
  symm
  apply Fintype.sum_of_injective (finiteCyclicIndex M q) (finiteCyclicIndex_injective hMq)
  · intro Y hY
    rw [cyclicZeroExtend_outside f Y hY, norm_zero, zero_pow (by decide)]
  · intro y
    rw [cyclicZeroExtend_original hMq]

/-- Restricting a full cyclic output to the original finite coordinates is contractive. -/
theorem finiteCyclicIndex_energy_le {M q : ℕ} [NeZero q] (hMq : M ≤ q) (F : ZMod q → ℂ) :
    (∑ y : Fin M, ‖F (finiteCyclicIndex M q y)‖ ^ 2) ≤ ∑ Y : ZMod q, ‖F Y‖ ^ 2 := by
  classical
  calc
    _ = ∑ Y ∈ Finset.univ.image (finiteCyclicIndex M q), ‖F Y‖ ^ 2 := by
      rw [Finset.sum_image]
      intro _ _ _ _ h
      exact finiteCyclicIndex_injective hMq h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

def horizontalEndpointIndex {N : ℕ} (x r : Fin N) : Fin (2 * N) :=
  ⟨x.val + r.val + 1, by have hx := x.isLt; have hr := r.isLt; omega⟩

/-- The original input and horizontal index are the same finite points. -/
theorem endpointIndex_horizontal {N : ℕ} (z : Base N) (r : Fin N) :
    (endpointIndex z r).1 = horizontalEndpointIndex z.1 r := rfl

/-- Every original shifted vertical point is represented by its actual input index. -/
theorem endpointIndex_cyclic {N q : ℕ} (z : Base N) (r : Fin N) :
    finiteCyclicIndex (N ^ 2) q z.2 + ((label r ^ 2 : ℕ) : ZMod q) =
      finiteCyclicIndex (2 * N ^ 2) q (endpointIndex z r).2 := by
  simp only [finiteCyclicIndex, endpointIndex, label, Nat.cast_add, Nat.cast_pow, Nat.cast_one]

def cyclicInput (N q : ℕ) (g : InputBox N → ℂ) (x : Fin (2 * N)) (Y : ZMod q) : ℂ :=
  cyclicZeroExtend (2 * N ^ 2) q (fun y => g (x, y)) Y

/-- Complete endpoint recovery, including both original vertical boundaries. -/
theorem cyclicInput_endpoint {N q : ℕ} (hq : 2 * N ^ 2 ≤ q)
    (g : InputBox N → ℂ) (z : Base N) (r : Fin N) :
    cyclicInput N q g (horizontalEndpointIndex z.1 r)
      (finiteCyclicIndex (N ^ 2) q z.2 + ((label r ^ 2 : ℕ) : ZMod q)) =
      g (endpointIndex z r) := by
  rw [endpointIndex_cyclic, cyclicInput, cyclicZeroExtend_original hq]
  rfl

theorem cyclicInput_energy {N q : ℕ} [NeZero q] (hq : 2 * N ^ 2 ≤ q)
    (g : InputBox N → ℂ) :
    (∑ x, ∑ Y, ‖cyclicInput N q g x Y‖ ^ 2) = ∑ u : InputBox N, ‖g u‖ ^ 2 := by
  simp only [cyclicInput, cyclicZeroExtend_energy hq, Fintype.sum_prod_type]

end GMZP0
