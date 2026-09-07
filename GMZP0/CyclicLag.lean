import GMZP0.CyclicOriginalFields

/-! The cyclic lag expression agrees exactly with the original one on its safe support. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem cyclicField_lag {V : Type*} {N q : ℕ} [NeZero q] (hq : N ^ 2 < q)
    (H : ℕ) (F : Base N → V) (fallback : V) (x : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (h k : ℤ)
    (hh : |h| ≤ H) (hk : |k| ≤ N) :
    cyclicField N q F fallback x (cyclicRow N q y + ((2 * h * k : ℤ) : ZMod q)) =
      originalFieldExtension N F fallback ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * k) := by
  have ht := safe_lag_target N H ((y.val : ℤ) + 1) h k hy (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh hk
  have hq' : (N : ℤ) ^ 2 < q := by exact_mod_cast hq
  exact cyclicField_shift F fallback x y (2 * h * k) (by omega) (ht.2.trans_lt hq')

theorem cyclicField_reroot_target {V : Type*} {N q : ℕ} [NeZero q] (hq : N ^ 2 < q)
    (H : ℕ) (F : Base N → V) (fallback : V) (x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (h t : ℤ)
    (hh : |h| ≤ H) (hHN : H ≤ N) (ht : t ∈ rerootLabels N h) :
    cyclicField N q F fallback x' (cyclicRow N q y + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)) =
      originalFieldExtension N F fallback ((x'.val : ℤ) + 1, (y.val : ℤ) + 1 + h ^ 2 + 2 * h * t) := by
  have ht' := (mem_rerootLabels_iff N h t).1 ht
  have hv := safe_parabola_target N H ((y.val : ℤ) + 1) h (t + h) hy
    (Nat.cast_nonneg _) (by exact_mod_cast hHN) hh (by omega) ht'.2.2
  have he : (y.val : ℤ) + 1 + 2 * h * (t + h) - h ^ 2 =
      (y.val : ℤ) + 1 + (h ^ 2 + 2 * h * t) := by ring
  rw [he] at hv
  have hq' : (N : ℤ) ^ 2 < q := by exact_mod_cast hq
  simpa only [add_assoc] using cyclicField_shift F fallback x' y (h ^ 2 + 2 * h * t)
    (by omega) (hv.2.trans_lt hq')

def cyclicLagG (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) : ℂ :=
  let z := v + ((2 * h * k : ℤ) : ZMod q)
  ((cyclicField N q σ 0 x z : ℝ) : ℂ) * conj (cyclicField N q lam 1 x z) *
    circleCharacter (-((t + h - k) ^ 3 • cyclicField N q p 0 x z))

def cyclicLagP (N q : ℕ) (p : Base N → Frequency) (x' : Fin N)
    (v : ZMod q) (h t k : ℤ) : Frequency :=
  -((t ^ 3 - (t - k) ^ 3) • cyclicField N q p 0 x'
    (v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)))

def cyclicLagB (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (v : ZMod q) (t : ℤ) : ℂ :=
  (∑ k ∈ lagInnerInterval N (horizontalGap x x') t,
    cyclicLagG N q p σ lam x v (horizontalGap x x') t k *
      circleCharacter (cyclicLagP N q p x' v (horizontalGap x x') t k)) / (N : ℂ)

theorem cyclicLagG_original {N q : ℕ} [NeZero q] (hq : N ^ 2 < q) (H : ℕ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x : Fin N) (y : Fin (N ^ 2)) (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (h t k : ℤ) (hh : |h| ≤ H) (hk : |k| ≤ N) :
    cyclicLagG N q p σ lam x (cyclicRow N q y) h t k = rerootedLagG N p σ lam x y h t k := by
  dsimp only [cyclicLagG, rerootedLagG]
  rw [cyclicField_lag hq H σ 0 x y hy h k hh hk,
    cyclicField_lag hq H lam 1 x y hy h k hh hk, cyclicField_lag hq H p 0 x y hy h k hh hk]

theorem cyclicLagP_original {N q : ℕ} [NeZero q] (hq : N ^ 2 < q) (H : ℕ)
    (p : Base N → Frequency) (x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (h t k : ℤ)
    (hh : |h| ≤ H) (hHN : H ≤ N) (ht : t ∈ rerootLabels N h) :
    cyclicLagP N q p x' (cyclicRow N q y) h t k = rerootedLagP N p x' y h t k := by
  dsimp only [cyclicLagP, rerootedLagP]
  rw [cyclicField_reroot_target hq H p 0 x' y hy h t hh hHN ht]

theorem cyclicLagB_original {N q : ℕ} [NeZero q] (hq : N ^ 2 < q) (H : ℕ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x x' : Fin N) (y : Fin (N ^ 2)) (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (t : ℤ) (hh : |horizontalGap x x'| ≤ H) (hHN : H ≤ N)
    (ht : t ∈ rerootLabels N (horizontalGap x x')) :
    cyclicLagB N q p σ lam x x' (cyclicRow N q y) t = rerootedLagB N p σ lam x x' y t := by
  unfold cyclicLagB rerootedLagB
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [cyclicLagG_original hq H p σ lam x y hy _ t k hh (le_of_lt (reroot_lag_bound N _ t k ht hk)),
    cyclicLagP_original hq H p x' y hy _ t k hh hHN ht]

/-- Equality of whole weighted vertical sums, requiring safety only where the original weight is nonzero. -/
theorem cyclic_weighted_B_norm_sum {N q : ℕ} [NeZero q] (hq : N ^ 2 < q) (H : ℕ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x x' : Fin N) (t : ℤ) (hh : |horizontalGap x x'| ≤ H) (hHN : H ≤ N)
    (ht : t ∈ rerootLabels N (horizontalGap x x'))
    (hsafe : ∀ y, σ (x, y) ≠ 0 → SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) :
    (∑ v : ZMod q, cyclicField N q σ 0 x v * ‖cyclicLagB N q p σ lam x x' v t‖) =
      ∑ y : Fin (N ^ 2), σ (x, y) * ‖rerootedLagB N p σ lam x x' y t‖ := by
  rw [cyclic_original_weighted_sum hq σ x]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hs : σ (x, y) = 0
  · simp only [hs, zero_mul]
  · rw [cyclicLagB_original hq H p σ lam x x' y (hsafe y hs) t hh hHN ht]

end GMZP0
