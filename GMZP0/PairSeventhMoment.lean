import GMZP0.PairDensity
import GMZP0.ExceptionalPairs
import GMZP0.LocalGoodFibers
import GMZP0.GlobalFrequencyAverage

/-! The core passage from a paired local average to a global seventh moment.
The family concatenation estimate is an explicit input, not a new axiom. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cyclicPairSeventhMean (N q s : ℕ) [NeZero q] (H : ZMod q → ℂ) : ℝ :=
  realUniformMean (fun z : Fin N × Fin N =>
    localCubeNorm 6 H (cyclicPairShiftMap q s (label z.1) (label z.2)))

theorem exists_good_cyclic_pair {N q s : ℕ} [NeZero q] (hN : 0 < N)
    (u : ℝ) (hu : 0 < u) (H : ZMod q → ℂ) (hH : ∀ y, ‖H y‖ ≤ 1)
    (hmean : u < cyclicPairSeventhMean N q s H) :
    ∃ z : Fin N × Fin N, N ≤ pairCutoff u * label z.1 ∧ N ≤ pairCutoff u * label z.2 ∧
      Nat.gcd (label z.1) (label z.2) ≤ pairCutoff u ∧
      u / 2 < localCubeNorm 6 H (cyclicPairShiftMap q s (label z.1) (label z.2)) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨z, hz, hlarge⟩ := exists_good_large_value
    (fun z : Fin N × Fin N => localCubeNorm 6 H (cyclicPairShiftMap q s (label z.1) (label z.2)))
    (pairExceptional N (pairCutoff u)) u hu
    (fun z => cyclicPairLocalSeven_le_one q s H hH _ _) hmean
    (exceptional_pair_probability_cutoff hN u hu)
  simp only [pairExceptional, not_or, not_lt] at hz
  exact ⟨z, hz.1, hz.2.1, hz.2.2, hlarge⟩

def pairSeventhLower (a u : ℝ) : ℝ :=
  (u / 2) ^ 128 / pairDensityConstant (pairCutoff u) a u ^ 7

theorem pairSeventhLower_pos (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    0 < pairSeventhLower a u := by
  unfold pairSeventhLower
  exact div_pos (pow_pos (by positivity) _) (pow_pos (pairDensityConstant_pos _ a u ha hu) _)

theorem global_seventh_from_pair_average {N q s : ℕ} [NeZero q]
    (hN : 0 < N) (hq : 4 * N ^ 2 < q) (hqUpper : q ≤ 128 * N ^ 2)
    (a u : ℝ) (ha : 0 < a) (hu : 0 < u) (hs : 2 * s < N) (hsLower : u * a * N / 256 ≤ s)
    (H : ZMod q → ℂ) (hH : ∀ y, ‖H y‖ ≤ 1) (hmean : u < cyclicPairSeventhMean N q s H) :
    pairSeventhLower a u ≤ globalCubeMoment 6 H := by
  obtain ⟨z, _, hlarge, hg, hlocal⟩ := exists_good_cyclic_pair hN u hu H hH hmean
  apply global_seventh_moment_of_good_pair hN hq hqUpper (pairCutoff_pos u hu)
    (by simp [label] : 0 < label z.1) (by simp only [label]; omega : label z.1 ≤ N)
    (by simp [label] : 0 < label z.2) (by simp only [label]; omega : label z.2 ≤ N)
    hs hlarge hg a u ha hu hsLower H hlocal.le

theorem cyclic_global_seventh_of_good_fibres {N q ℓ M s : ℕ} [NeZero q]
    (hN : 0 < N) (hq : 4 * N ^ 2 < q) (hqUpper : q ≤ 128 * N ^ 2)
    (a u β : ℝ) (ha : 0 < a) (hu : 0 < u)
    (hs : 2 * s < N) (hsLower : u * a * N / 256 ≤ s)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (hgood : β / 2 ≤ cyclicLocalGoodFiberMass N q ℓ M σ F β)
    (hfamily : ∀ x j, β / 2 ≤ cyclicLocalFourFiber N q ℓ M σ F x j →
      u < cyclicPairSeventhMean N q s (modulatedCyclicField N q M σ F x j)) :
    β / 2 * pairSeventhLower a u ≤ cyclicGlobalSeventhMoment N q M σ F := by
  classical
  have hpoint (z : Fin N × Fin (1024 * M)) :
      pairSeventhLower a u * (if β / 2 ≤ cyclicLocalFourFiber N q ℓ M σ F z.1 z.2 then 1 else 0) ≤
        globalCubeMoment 6 (modulatedCyclicField N q M σ F z.1 z.2) := by
    split_ifs with hz
    · rw [mul_one]
      exact global_seventh_from_pair_average hN hq hqUpper a u ha hu hs hsLower
        _ (modulatedCyclicField_norm_le N q M σ F hσ z.1 z.2) (hfamily _ _ hz)
    · rw [mul_zero]
      exact globalCubeMoment_nonneg 6 _
  have hm := realUniformMean_mono _ _ hpoint
  rw [realUniformMean_const_mul] at hm
  have he := realUniformMean_prod (fun (x : Fin N) (j : Fin (1024 * M)) =>
    globalCubeMoment 6 (modulatedCyclicField N q M σ F x j))
  rw [he] at hm
  have hg := mul_le_mul_of_nonneg_left hgood (pairSeventhLower_pos a u ha hu).le
  calc
    _ ≤ pairSeventhLower a u * cyclicLocalGoodFiberMass N q ℓ M σ F β := by
      simpa only [mul_comm] using hg
    _ ≤ _ := hm

theorem cyclic_real_seven_of_pair_family {N q ℓ M s : ℕ} [NeZero q]
    (hN : 0 < N) (hM : 0 < M) (hq : 4 * N ^ 2 < q) (hqUpper : q ≤ 128 * N ^ 2)
    (a u β : ℝ) (ha : 0 < a) (hu : 0 < u)
    (hs : 2 * s < N) (hsLower : u * a * N / 256 ≤ s)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (hgrid : ∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) (hF : ∀ x Y, |F x Y| ≤ 3)
    (hgood : β / 2 ≤ cyclicLocalGoodFiberMass N q ℓ M σ F β)
    (hfamily : ∀ x j, β / 2 ≤ cyclicLocalFourFiber N q ℓ M σ F x j →
      u < cyclicPairSeventhMean N q s (modulatedCyclicField N q M σ F x j)) :
    β / 2 * pairSeventhLower a u ≤ cyclicGlobalRealSevenMass N q σ F := by
  rw [← cyclicGlobalSeventhMoment_eq_mass hM σ F hgrid hF]
  exact cyclic_global_seventh_of_good_fibres hN hq hqUpper a u β ha hu hs hsLower σ F hσ hgood hfamily

end GMZP0
