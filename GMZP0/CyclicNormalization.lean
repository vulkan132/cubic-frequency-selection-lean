import GMZP0.CyclicLag
import GMZP0.HorizontalShiftReindexing

/-! Exact cyclic modulus average and the factor 2q/N² from its complete sampling ranges. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cyclicShiftLagP (N q : ℕ) (p : Base N → Frequency) (x : Fin N)
    (v : ZMod q) (h t k : ℤ) : Frequency :=
  -((t ^ 3 - (t - k) ^ 3) • originalFieldExtension N p 0
    ((x.val : ℤ) + 1 + h, ((v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)).val : ℤ)))

def cyclicShiftLagB (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t : ℤ) : ℂ :=
  (∑ k ∈ lagInnerInterval N h t, cyclicLagG N q p σ lam x v h t k *
    circleCharacter (cyclicShiftLagP N q p x v h t k)) / (N : ℂ)

theorem cyclicShiftLagP_gap (N q : ℕ) (p : Base N → Frequency) (x x' : Fin N)
    (v : ZMod q) (t k : ℤ) :
    cyclicShiftLagP N q p x v (horizontalGap x x') t k =
      cyclicLagP N q p x' v (horizontalGap x x') t k := by
  have he : (x.val : ℤ) + 1 + horizontalGap x x' = (x'.val : ℤ) + 1 := by
    unfold horizontalGap
    ring
  dsimp only [cyclicShiftLagP, cyclicLagP, cyclicField]
  rw [he]

theorem cyclicShiftLagB_gap (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (v : ZMod q) (t : ℤ) :
    cyclicShiftLagB N q p σ lam x v (horizontalGap x x') t = cyclicLagB N q p σ lam x x' v t := by
  unfold cyclicShiftLagB cyclicLagB
  simp_rw [cyclicShiftLagP_gap]

def cyclicPairNormNumerator (N q : ℕ) [NeZero q] (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ t ∈ rerootLabels N (horizontalGap x x'), ∑ v : ZMod q,
      cyclicField N q σ 0 x v * ‖cyclicLagB N q p σ lam x x' v t‖ else 0

def cyclicShiftNormNumerator (N q : ℕ) [NeZero q] (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ h ∈ horizontalShiftLabels N, if x ∈ X ∧ horizontalShiftIn X x h then
    ∑ t ∈ rerootLabels N h, ∑ v : ZMod q,
      cyclicField N q σ 0 x v * ‖cyclicShiftLagB N q p σ lam x v h t‖ else 0

/-- A uniform average on every x, nonzero h, cyclic y, and original label t, with its indicators. -/
def cyclicModulusAverage (N q : ℕ) [NeZero q] (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  (∑ x : Fin N, ∑ h ∈ horizontalShiftLabels N, if x ∈ X ∧ horizontalShiftIn X x h then
    ∑ v : ZMod q, ∑ t : Fin N, if 1 ≤ (label t : ℤ) + h ∧ (label t : ℤ) + h ≤ N then
      cyclicField N q σ 0 x v * ‖cyclicShiftLagB N q p σ lam x v h (label t)‖ else 0 else 0) /
        (2 * (q : ℝ) * (N : ℝ) ^ 3)

theorem cyclicPairNormNumerator_original {N q : ℕ} [NeZero q] (hq : N ^ 2 < q)
    (H : ℕ) (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hHN : H ≤ N) (hX : ∀ x ∈ X, ∀ x' ∈ X, |horizontalGap x x'| ≤ H)
    (hsafe : ∀ x y, σ (x, y) ≠ 0 → SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) :
    cyclicPairNormNumerator N q p X σ lam = rerootedNormSum N p X σ lam := by
  unfold cyclicPairNormNumerator rerootedNormSum
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  split_ifs with hx
  · conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    exact cyclic_weighted_B_norm_sum hq H p σ lam x x' t (hX x hx.1 x' hx.2.1) hHN ht (hsafe x)
  · rfl

theorem cyclicPairNormNumerator_shift (N q : ℕ) [NeZero q] (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicPairNormNumerator N q p X σ lam = cyclicShiftNormNumerator N q p X σ lam := by
  unfold cyclicPairNormNumerator cyclicShiftNormNumerator
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ X
  · simp only [hx, true_and]
    simp_rw [← cyclicShiftLagB_gap]
    exact horizontal_shift_sum X x (fun h => ∑ t ∈ rerootLabels N h, ∑ v : ZMod q,
      cyclicField N q σ 0 x v * ‖cyclicShiftLagB N q p σ lam x v h t‖)
  · simp only [hx, false_and, if_false, Finset.sum_const_zero]

theorem cyclicModulusAverage_eq (N q : ℕ) [NeZero q] (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicModulusAverage N q p X σ lam =
      cyclicShiftNormNumerator N q p X σ lam / (2 * (q : ℝ) * (N : ℝ) ^ 3) := by
  unfold cyclicModulusAverage cyclicShiftNormNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro h _
  split_ifs
  · conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact (sum_rerootLabels N h (fun t => cyclicField N q σ 0 x v *
      ‖cyclicShiftLagB N q p σ lam x v h t‖)).symm
  · rfl

/-- The exact sampling conversion: the original finite average equals (2q/N²) times the cyclic average. -/
theorem finite_to_cyclic_modulus_average {N q : ℕ} [NeZero q] (hN : 0 < N) (hq : N ^ 2 < q)
    (H : ℕ) (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hHN : H ≤ N) (hX : ∀ x ∈ X, ∀ x' ∈ X, |horizontalGap x x'| ≤ H)
    (hsafe : ∀ x y, σ (x, y) ≠ 0 → SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) :
    finiteRerootedNormAverage N p X σ lam =
      (2 * (q : ℝ) / (N : ℝ) ^ 2) * cyclicModulusAverage N q p X σ lam := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [finiteRerootedNormAverage_eq, ← cyclicPairNormNumerator_original hq H p X σ lam hHN hX hsafe,
    cyclicPairNormNumerator_shift, cyclicModulusAverage_eq]
  field_simp

/-- The upper modulus bound q<=128N² converts the exact positive finite input into the paper's a=ζ/128. -/
theorem cyclic_average_positive_of_finite {N q : ℕ} [NeZero q] (hN : 0 < N) (hq : N ^ 2 < q)
    (hqUpper : q ≤ 128 * N ^ 2) (H : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) (ζ : ℝ) (hζ : 0 < ζ)
    (hHN : H ≤ N) (hX : ∀ x ∈ X, ∀ x' ∈ X, |horizontalGap x x'| ≤ H)
    (hsafe : ∀ x y, σ (x, y) ≠ 0 → SafeVertical (N : ℤ) H ((y.val : ℤ) + 1))
    (hpositive : 2 * ζ ≤ finiteRerootedNormAverage N p X σ lam) :
    ζ / 128 ≤ cyclicModulusAverage N q p X σ lam := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqU : (q : ℝ) ≤ 128 * (N : ℝ) ^ 2 := by exact_mod_cast hqUpper
  rw [finite_to_cyclic_modulus_average hN hq H p X σ lam hHN hX hsafe] at hpositive
  have he : ((2 * (q : ℝ) / (N : ℝ) ^ 2) * cyclicModulusAverage N q p X σ lam) * (N : ℝ) ^ 2 =
      2 * (q : ℝ) * cyclicModulusAverage N q p X σ lam := by field_simp
  have hp := mul_le_mul_of_nonneg_right hpositive (sq_nonneg (N : ℝ))
  rw [he] at hp
  calc
    ζ / 128 ≤ ζ * (N : ℝ) ^ 2 / (q : ℝ) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 128) hqr).2
      nlinarith only [mul_le_mul_of_nonneg_left hqU hζ.le]
    _ ≤ cyclicModulusAverage N q p X σ lam := by
      apply (div_le_iff₀ hqr).2
      nlinarith only [hp]

end GMZP0
