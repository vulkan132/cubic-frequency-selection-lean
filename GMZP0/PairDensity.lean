import GMZP0.PairRepresentations
import GMZP0.ParameterEnergy
import GMZP0.LocalGlobalComparison

/-! Explicit uniform density energy and the resulting seventh moment for actual good pairs. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cyclic_pair_density_energy {N q s A h h' : ℕ} [NeZero q]
    (hN : 0 < N) (hq : 4 * N ^ 2 < q) (hA : 0 < A)
    (hh : 0 < h) (hhN : h ≤ N) (hh' : 0 < h') (hh'N : h' ≤ N)
    (hs : 2 * s < N) (hlarge : N ≤ A * h') (hg : Nat.gcd h h' ≤ A) :
    realUniformMean (fun y : ZMod q => parameterDensity (cyclicPairShiftMap q s h h') y ^ 2) ≤
      (q : ℝ) * (1 + 2 * (A : ℝ) ^ 2) / (2 * (s : ℝ) + 1) ^ 2 := by
  have he := parameterDensity_energy_le (cyclicPairShiftMap q s h h') (1 + 2 * A ^ 2)
    (cyclic_pair_representation_count hN hq hA hh hhN hh' hh'N hs hlarge hg)
  simpa only [ZMod.card, Fintype.card_prod, Fintype.card_coe, card_smoothingShiftLabels,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, pow_two] using he

theorem pair_density_scale_bound {N q s A : ℕ} (hN : 0 < N) (hq : q ≤ 128 * N ^ 2)
    (a u : ℝ) (ha : 0 < a) (hu : 0 < u) (hs : u * a * N / 256 ≤ s) :
    (q : ℝ) * (1 + 2 * (A : ℝ) ^ 2) / (2 * (s : ℝ) + 1) ^ 2 ≤
      2 ^ 24 * (1 + 2 * (A : ℝ) ^ 2) / (u ^ 2 * a ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (q : ℝ) ≤ 128 * (N : ℝ) ^ 2 := by exact_mod_cast hq
  have hden : 0 < (2 * (s : ℝ) + 1) ^ 2 := by positivity
  have hua : 0 < u ^ 2 * a ^ 2 := by positivity
  have hprod : 0 < u * a * N := by positivity
  have hstep : u * a * N ≤ 256 * (2 * (s : ℝ) + 1) := by nlinarith [Nat.cast_nonneg s (α := ℝ)]
  have hsq : (u * a * N) ^ 2 ≤ (256 * (2 * (s : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hprod.le hstep 2
  have hqmul := mul_le_mul_of_nonneg_right hqr hua.le
  have hbase : (q : ℝ) * (u ^ 2 * a ^ 2) ≤ 2 ^ 24 * (2 * (s : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (2 * (s : ℝ) + 1)]
  apply (div_le_div_iff₀ hden hua).mpr
  calc
    _ = ((q : ℝ) * (u ^ 2 * a ^ 2)) * (1 + 2 * (A : ℝ) ^ 2) := by ring
    _ ≤ (2 ^ 24 * (2 * (s : ℝ) + 1) ^ 2) * (1 + 2 * (A : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = _ := by ring

def pairDensityConstant (A : ℕ) (a u : ℝ) : ℝ :=
  2 ^ 24 * (1 + 2 * (A : ℝ) ^ 2) / (u ^ 2 * a ^ 2)

theorem pairDensityConstant_pos (A : ℕ) (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    0 < pairDensityConstant A a u := by
  unfold pairDensityConstant
  positivity

theorem cyclic_pair_density_uniform {N q s A h h' : ℕ} [NeZero q]
    (hN : 0 < N) (hq : 4 * N ^ 2 < q) (hqUpper : q ≤ 128 * N ^ 2) (hA : 0 < A)
    (hh : 0 < h) (hhN : h ≤ N) (hh' : 0 < h') (hh'N : h' ≤ N)
    (hs : 2 * s < N) (hlarge : N ≤ A * h') (hg : Nat.gcd h h' ≤ A)
    (a u : ℝ) (ha : 0 < a) (hu : 0 < u) (hsLower : u * a * N / 256 ≤ s) :
    realUniformMean (fun y : ZMod q => parameterDensity (cyclicPairShiftMap q s h h') y ^ 2) ≤
      pairDensityConstant A a u :=
  (cyclic_pair_density_energy hN hq hA hh hhN hh' hh'N hs hlarge hg).trans
    (pair_density_scale_bound hN hqUpper a u ha hu hsLower)

theorem global_seventh_moment_of_good_pair {N q s A h h' : ℕ} [NeZero q]
    (hN : 0 < N) (hq : 4 * N ^ 2 < q) (hqUpper : q ≤ 128 * N ^ 2) (hA : 0 < A)
    (hh : 0 < h) (hhN : h ≤ N) (hh' : 0 < h') (hh'N : h' ≤ N)
    (hs : 2 * s < N) (hlarge : N ≤ A * h') (hg : Nat.gcd h h' ≤ A)
    (a u : ℝ) (ha : 0 < a) (hu : 0 < u) (hsLower : u * a * N / 256 ≤ s)
    (H : ZMod q → ℂ) (hLocal : u / 2 ≤ localCubeNorm 6 H (cyclicPairShiftMap q s h h')) :
    (u / 2) ^ 128 / pairDensityConstant A a u ^ 7 ≤ globalCubeMoment 6 H := by
  exact globalCubeMoment_lower_from_local 5 H _ (pairDensityConstant A a u) (u / 2)
    (pairDensityConstant_pos A a u ha hu) (by positivity)
    (cyclic_pair_density_uniform hN hq hqUpper hA hh hhN hh' hh'N hs hlarge hg a u ha hu hsLower)
    hLocal

end GMZP0
