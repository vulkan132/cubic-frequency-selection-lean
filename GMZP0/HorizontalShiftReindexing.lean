import GMZP0.RerootedAverage

/-! Reindex horizontal target indices by every nonzero shift in [-N,N]. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def horizontalShiftLabels (N : ℕ) : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0

def horizontalShiftIn {N : ℕ} (X : Finset (Fin N)) (x : Fin N) (h : ℤ) : Prop :=
  ∃ x' ∈ X, (x'.val : ℤ) + 1 = (x.val : ℤ) + 1 + h

instance {N : ℕ} (X : Finset (Fin N)) (x : Fin N) (h : ℤ) : Decidable (horizontalShiftIn X x h) := by
  unfold horizontalShiftIn
  infer_instance

theorem horizontalGap_bound {N : ℕ} (x x' : Fin N) : |horizontalGap x x'| < N := by
  have hx := x.isLt
  have hx' := x'.isLt
  unfold horizontalGap
  apply abs_lt.mpr
  constructor <;> omega

theorem horizontalShiftLabels_card (N : ℕ) : (horizontalShiftLabels N).card = 2 * N := by
  have hz : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by simp
  rw [horizontalShiftLabels, Finset.card_erase_of_mem hz, Int.card_Icc]
  have he : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, Int.toNat_natCast]
  omega

/-- Complete equality for arbitrary shift functions; shifts missing the original X contribute zero. -/
theorem horizontal_shift_sum {N : ℕ} (X : Finset (Fin N)) (x : Fin N) (F : ℤ → ℝ) :
    (∑ x' : Fin N, if x' ∈ X ∧ x' ≠ x then F (horizontalGap x x') else 0) =
      ∑ h ∈ horizontalShiftLabels N, if horizontalShiftIn X x h then F h else 0 := by
  classical
  calc
    (∑ x' : Fin N, if x' ∈ X ∧ x' ≠ x then F (horizontalGap x x') else 0) =
        ∑ x' ∈ Finset.univ.filter (fun x' => x' ∈ X ∧ x' ≠ x), F (horizontalGap x x') := by
      rw [Finset.sum_filter]
    _ = ∑ h ∈ (horizontalShiftLabels N).filter (horizontalShiftIn X x), F h := by
      apply Finset.sum_bij (fun x' _ => horizontalGap x x')
      · intro x' hx'
        have hx'X := (Finset.mem_filter.mp hx').2
        have hb := abs_lt.mp (horizontalGap_bound x x')
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_erase.mpr ⟨horizontalGap_ne_zero x x' hx'X.2.symm,
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
        refine ⟨x', hx'X.1, ?_⟩
        unfold horizontalGap
        ring
      · intro x' hx' u hu he
        apply Fin.ext
        unfold horizontalGap at he
        omega
      · intro h hh
        have hmem := (Finset.mem_filter.mp hh)
        have hn : h ≠ 0 := (Finset.mem_erase.mp hmem.1).1
        obtain ⟨x', hx'X, he⟩ := hmem.2
        have hgap : horizontalGap x x' = h := by unfold horizontalGap; omega
        have hne : x' ≠ x := by
          intro hxx'
          apply hn
          rw [← hgap, hxx']
          simp only [horizontalGap, sub_self]
        exact ⟨x', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'X, hne⟩, hgap⟩
      · intro x' hx'
        rfl
    _ = _ := by rw [Finset.sum_filter]

end GMZP0
