import GMZP0.PositiveCyclicAverage
import Mathlib.NumberTheory.Bertrand

/-! A prime in the manuscript's strict modulus range, obtained from the checked Bertrand theorem. -/

noncomputable section
namespace GMZP0

theorem exists_prime_cyclic_modulus {N : ℕ} (hN : 0 < N) :
    ∃ q : ℕ, Nat.Prime q ∧ 64 * N ^ 2 < q ∧ q < 128 * N ^ 2 := by
  obtain ⟨q, hp, hl, hu⟩ := Nat.exists_prime_lt_and_le_two_mul (64 * N ^ 2)
    (mul_ne_zero (by decide) (pow_ne_zero 2 hN.ne'))
  refine ⟨q, hp, hl, ?_⟩
  have hu' : q ≤ 128 * N ^ 2 := by nlinarith only [hu]
  by_contra hn
  have he : q = 128 * N ^ 2 := le_antisymm hu' (le_of_not_gt hn)
  have hd : 2 ∣ q := by
    refine ⟨64 * N ^ 2, ?_⟩
    rw [he]
    ring
  have hq2 := ((Nat.dvd_prime hp).1 hd).resolve_left (by decide : (2 : ℕ) ≠ 1)
  have hpow : 0 < N ^ 2 := pow_pos hN 2
  omega

end GMZP0
