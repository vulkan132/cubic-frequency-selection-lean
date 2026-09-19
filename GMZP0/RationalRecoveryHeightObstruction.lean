import Mathlib.Data.Rat.Lemmas

/-! Even a one-dimensional rational recovery problem can have unbounded
denominator as its structural coefficient varies. Rational existence or
fixed degree alone cannot justify a uniform height claim. -/
namespace GMZP0

/-- The inverse of evaluation by the nonzero integer n has denominator
exactly n, already in a one-dimensional constant-polynomial example. -/
theorem rational_scalar_recovery_denominator (n : ℕ) (hn : 0 < n)
    (a : ℚ) (ha : a * (n : ℚ) = 1) : a.den = n := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he : a = (n : ℚ)⁻¹ := by simpa only [one_div] using (eq_div_iff hn0).mpr ha
  rw [he, Rat.inv_natCast_den, if_neg hn.ne']

/-- No denominator bound follows from rationality and one-dimensionality
alone. This is a scope obstruction, not a counterexample to P0. -/
theorem rational_scalar_recovery_no_uniform_height :
    ¬ ∃ H : ℕ, ∀ n : ℕ, 0 < n → ∃ a : ℚ, a * (n : ℚ) = 1 ∧ a.den ≤ H := by
  rintro ⟨H, hH⟩
  obtain ⟨a, ha, hbound⟩ := hH (H + 1) (Nat.succ_pos H)
  rw [rational_scalar_recovery_denominator (H + 1) (Nat.succ_pos H) a ha] at hbound
  exact Nat.not_succ_le_self H hbound

end GMZP0
