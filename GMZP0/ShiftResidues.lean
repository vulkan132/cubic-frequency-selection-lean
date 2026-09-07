import GMZP0.CubeSignSymmetry

/-! The short shift interval injects into the cyclic group before collision probabilities are used. -/

noncomputable section
namespace GMZP0

theorem smoothingShift_cast_injective {q ℓ : ℕ} (hℓ : 2 * ℓ < q) :
    Function.Injective (fun a : smoothingShiftLabels ℓ => (a.val : ZMod q)) := by
  intro a b he
  change (a.val : ZMod q) = (b.val : ZMod q) at he
  have ha := a.property
  have hb := b.property
  simp only [smoothingShiftLabels, Finset.mem_Icc] at ha hb
  have hcast : ((a.val + (ℓ : ℤ) : ℤ) : ZMod q) = ((b.val + (ℓ : ℤ) : ℤ) : ZMod q) := by
    push_cast
    rw [he]
  have hr := (ZMod.intCast_eq_intCast_iff' (a.val + (ℓ : ℤ)) (b.val + (ℓ : ℤ)) q).mp hcast
  have haq : a.val + (ℓ : ℤ) < (q : ℤ) := by omega
  have hbq : b.val + (ℓ : ℤ) < (q : ℤ) := by omega
  rw [Int.emod_eq_of_lt (by omega) haq, Int.emod_eq_of_lt (by omega) hbq] at hr
  apply Subtype.ext
  omega

theorem positive_cube_step_ne_zero {N q : ℕ} (hq : 2 * N < q) (h : Fin N) :
    ((2 * (label h : ℤ) : ℤ) : ZMod q) ≠ 0 := by
  have hh := integer_label_bounds h
  have hs0 : (0 : ℤ) < 2 * (label h : ℤ) := by omega
  have hsq : 2 * (label h : ℤ) < (q : ℤ) := by omega
  intro he
  have hm := (ZMod.intCast_eq_intCast_iff' (2 * (label h : ℤ)) 0 q).mp (by simpa using he)
  rw [Int.emod_eq_of_lt hs0.le hsq, Int.zero_emod] at hm
  omega

end GMZP0
