import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! The integer quotient by 2Z illustrates why a general integer quotient
cannot be treated as torsion-free or supplied with an additive section.
The observation quotient avoids this obstruction by its checked embedding into V/W. -/
namespace GMZP0

/-- The exact quotient Z/2Z contains a nonzero element killed by a nonzero integer. -/
theorem integer_quotient_torsion_obstruction :
    (2 : ℤ) • (1 : ZMod 2) = 0 ∧ (1 : ZMod 2) ≠ 0 := by
  decide

/-- The quotient map Z -> Z/2Z has no additive section. -/
theorem integer_quotient_section_obstruction :
    ¬ ∃ s : ZMod 2 →+ ℤ, ∀ x : ZMod 2, (s x : ZMod 2) = x := by
  rintro ⟨s, hs⟩
  have hz : (2 : ℤ) • s (1 : ZMod 2) = 0 := by
    rw [← map_zsmul, integer_quotient_torsion_obstruction.1, map_zero]
  have hs0 : s (1 : ZMod 2) = 0 := by
    have hz' : 2 * s (1 : ZMod 2) = 0 := by simpa [zsmul_eq_mul] using hz
    exact (mul_eq_zero.mp hz').resolve_left (by norm_num)
  have he := hs 1
  rw [hs0, Int.cast_zero] at he
  exact zero_ne_one he

end GMZP0
