import GMZP0.BlockCollisions

/-! Integer geometry ensuring that a safe-window collision reads the original frequency field. -/

noncomputable section
namespace GMZP0

def SafeVertical (N H y : ℤ) : Prop := 3 * H * N + 1 ≤ y ∧ y ≤ N ^ 2 - 3 * H * N

/-- The shift bound uses both |h| <= H <= N and the actual label range. -/
theorem parabola_shift_abs_le (N H h r : ℤ) (hH : 0 ≤ H) (hHN : H ≤ N)
    (hh : |h| ≤ H) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
    |2 * h * r - h ^ 2| ≤ 3 * H * N := by
  have hprod : |h| * r ≤ H * N :=
    mul_le_mul hh hrN hr0 hH
  have hsq : |h| ^ 2 ≤ H * N := by
    calc
      |h| ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
      _ ≤ H * N := by nlinarith only [mul_le_mul_of_nonneg_left hHN hH]
  calc
    |2 * h * r - h ^ 2| ≤ |2 * h * r| + |h ^ 2| := abs_sub _ _
    _ = 2 * (|h| * r) + |h| ^ 2 := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), abs_of_nonneg hr0, abs_pow]
      ring
    _ ≤ 3 * H * N := by nlinarith only [hprod, hsq]

theorem safe_vertical_shift (N H y d : ℤ) (hy : SafeVertical N H y)
    (hd : |d| ≤ 3 * H * N) : 1 ≤ y + d ∧ y + d ≤ N ^ 2 := by
  obtain ⟨hlo, hhi⟩ := hy
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  constructor <;> omega

theorem safe_parabola_target (N H y h r : ℤ) (hy : SafeVertical N H y)
    (hH : 0 ≤ H) (hHN : H ≤ N) (hh : |h| ≤ H) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
    1 ≤ y + 2 * h * r - h ^ 2 ∧ y + 2 * h * r - h ^ 2 ≤ N ^ 2 := by
  simpa only [add_sub_assoc] using
    safe_vertical_shift N H y (2 * h * r - h ^ 2) hy
      (parabola_shift_abs_le N H h r hH hHN hh hr0 hrN)

/-- The second base point displaced by 2hk also stays in the box in the full label range. -/
theorem safe_lag_target (N H y h k : ℤ) (hy : SafeVertical N H y)
    (hH : 0 ≤ H) (hN : 0 ≤ N) (hh : |h| ≤ H) (hk : |k| ≤ N) :
    1 ≤ y + 2 * h * k ∧ y + 2 * h * k ≤ N ^ 2 := by
  apply safe_vertical_shift N H y (2 * h * k) hy
  have hp : |h| * |k| ≤ H * N := mul_le_mul hh hk (abs_nonneg _) hH
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
  nlinarith [mul_nonneg hH hN]

/-- Every integer point in an original vertical fiber has an actual finite base index. -/
theorem exists_original_vertical_point {N : ℕ} (x : Fin N) (t : ℤ)
    (ht0 : 1 ≤ t) (htN : t ≤ (N : ℤ) ^ 2) :
    ∃ w : Base N, w.1 = x ∧ basePoint w = ((x.val : ℤ) + 1, t) := by
  have htN' : t ≤ (N ^ 2 : ℕ) := by exact_mod_cast htN
  let v : Fin (N ^ 2) := ⟨(t - 1).toNat, by omega⟩
  refine ⟨(x, v), rfl, ?_⟩
  apply Prod.ext
  · rfl
  · change ((t - 1).toNat : ℤ) + 1 = t
    omega

/-- Safe-window target evaluations can use an original base point, with no extension of p. -/
theorem safe_original_target_exists {N : ℕ} (x' : Fin N) (H y h r : ℤ)
    (hy : SafeVertical (N : ℤ) H y) (hH : 0 ≤ H) (hHN : H ≤ N)
    (hh : |h| ≤ H) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
    ∃ w : Base N, w.1 = x' ∧
      basePoint w = ((x'.val : ℤ) + 1, y + 2 * h * r - h ^ 2) := by
  have ht := safe_parabola_target N H y h r hy hH hHN hh hr0 hrN
  exact exists_original_vertical_point x' _ ht.1 ht.2

theorem horizontal_interval_gap (a H x x' : ℤ)
    (hx : a ≤ x ∧ x ≤ a + H) (hx' : a ≤ x' ∧ x' ≤ a + H) : |x' - x| ≤ H := by
  apply abs_le.mpr
  constructor <;> omega

/-- On a nonzero horizontal displacement, a zero vertical lag is exactly k=0. -/
theorem vertical_lag_zero_iff (y h k : ℤ) (hh : h ≠ 0) :
    y + 2 * h * k = y ↔ k = 0 := by
  constructor
  · intro he
    have hp : (2 * h) * k = 0 := by omega
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (by decide) hh)
  · intro hk
    simp [hk]

end GMZP0
