import GMZP0.RerootedPhase
import GMZP0.ZeroLag

/-! Complete rerooted weighted sum with its exact original-scale normalization. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def rerootedWeightedSum (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ t ∈ rerootLabels N (horizontalGap x x'),
      σ (x, y) * (rerootedOuterPhase N p lam x y (horizontalGap x x') t *
        rerootedLagB N p σ lam x x' y t).re else 0

/-- Rerooting the entire sum produces N times the outer sum of the N-normalized B. -/
theorem fullLagNumerator_reroot {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    fullLagNumerator N p X σ lam = rerootedWeightedSum N p X σ lam * (N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold fullLagNumerator rerootedWeightedSum
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  split_ifs
  · apply Finset.sum_congr rfl
    intro y _
    rw [lag_sum_reroot]
    apply Finset.sum_congr rfl
    intro t _
    exact (div_eq_iff hNr).1 (rerooted_inner_average N p σ lam x x' y t)
  · rfl

/-- The exact normalization after absorbing the 1/N in B is N^(-5). -/
theorem fullLagStatistic_reroot {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    fullLagStatistic N p X σ lam = rerootedWeightedSum N p X σ lam / (N : ℝ) ^ 5 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [fullLagStatistic, fullLagNumerator_reroot hN]
  field_simp

/-- Both diagonal origins remain explicit when the signed statistic enters the rerooted expression. -/
theorem signed_plus_diagonal_reroot {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    lagSignedDoubleStatistic N p X σ lam + lagDiagonalStatistic N p X σ lam =
      rerootedWeightedSum N p X σ lam / (N : ℝ) ^ 5 := by
  rw [← fullLagStatistic_split, fullLagStatistic_reroot hN]

end GMZP0
