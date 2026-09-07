import GMZP0.LagStatistic
import GMZP0.Rerooting

/-! Exact separation of the rerooted lag phase into the original weighted g and cubic P. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def rerootedLagG (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (y : Fin (N ^ 2)) (h t k : ℤ) : ℂ :=
  let z := ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * k)
  ((originalFieldExtension N σ 0 z : ℝ) : ℂ) * conj (originalFieldExtension N lam 1 z) *
    circleCharacter (-((t + h - k) ^ 3 • originalFieldExtension N p 0 z))

def rerootedLagP (N : ℕ) (p : Base N → Frequency) (x' : Fin N)
    (y : Fin (N ^ 2)) (h t k : ℤ) : Frequency :=
  -((t ^ 3 - (t - k) ^ 3) • originalFieldExtension N p 0
    ((x'.val : ℤ) + 1, (y.val : ℤ) + 1 + h ^ 2 + 2 * h * t))

def rerootedLagB (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (t : ℤ) : ℂ :=
  (∑ k ∈ lagInnerInterval N (horizontalGap x x') t,
    rerootedLagG N p σ lam x y (horizontalGap x x') t k *
      circleCharacter (rerootedLagP N p x' y (horizontalGap x x') t k)) / (N : ℂ)

def rerootedOuterPhase (N : ℕ) (p : Base N → Frequency) (lam : Base N → ℂ)
    (x : Fin N) (y : Fin (N ^ 2)) (h t : ℤ) : ℂ :=
  lam (x, y) * circleCharacter ((t + h) ^ 3 • p (x, y))

theorem originalLagSummand_reroot (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (t k : ℤ) :
    originalLagSummand N p σ lam x x' y k (t - k + horizontalGap x x') =
      σ (x, y) * (rerootedOuterPhase N p lam x y (horizontalGap x x') t *
        (rerootedLagG N p σ lam x y (horizontalGap x x') t k *
          circleCharacter (rerootedLagP N p x' y (horizontalGap x x') t k))).re := by
  have hv : (y.val : ℤ) + 1 + 2 * horizontalGap x x' *
      (t - k + horizontalGap x x' + k) - horizontalGap x x' ^ 2 =
      (y.val : ℤ) + 1 + horizontalGap x x' ^ 2 + 2 * horizontalGap x x' * t := by ring
  dsimp only [originalLagSummand, rerootedOuterPhase, rerootedLagG, rerootedLagP]
  rw [hv, doublePhaseCoefficient_reroot]
  simp only [circleCharacter_sub, circleCharacter_neg]
  have hscalar (s : ℝ) (l m A B C : ℂ) :
      s * (l * m * (A * B * C)).re = (l * A * (((s : ℂ) * m * B) * C)).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    ring
  rw [mul_assoc, hscalar]

/-- The interval sum and B use exactly N normalization, independently of its shorter actual length. -/
theorem rerooted_inner_average (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (t : ℤ) :
    (∑ k ∈ lagInnerInterval N (horizontalGap x x') t,
      originalLagSummand N p σ lam x x' y k (t - k + horizontalGap x x')) / (N : ℝ) =
      σ (x, y) * (rerootedOuterPhase N p lam x y (horizontalGap x x') t *
        rerootedLagB N p σ lam x x' y t).re := by
  simp_rw [originalLagSummand_reroot]
  rw [rerootedLagB, ← mul_div_assoc]
  have hc : (N : ℂ) = ((N : ℝ) : ℂ) := by norm_cast
  rw [hc, Complex.div_ofReal_re, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.mul_sum]
  ring

end GMZP0
