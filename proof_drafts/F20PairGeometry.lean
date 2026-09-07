import GMZP0.WeightedCollisionRemoval
import GMZP0.CyclicLocalCube

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem exists_good_large_value {I : Type*} [Fintype I] [Nonempty I]
    (T : I → ℝ) (bad : I → Prop) [DecidablePred bad] (u : ℝ) (hu : 0 < u)
    (hT : ∀ i, T i ≤ 1) (hmean : u < realUniformMean T)
    (hbad : realUniformMean (fun i => if bad i then 1 else 0) ≤ u / 4) :
    ∃ i, ¬ bad i ∧ u / 2 < T i := by
  by_contra! hn
  have hp (i : I) : T i ≤ (if bad i then 1 else 0) + u / 2 := by
    by_cases hb : bad i
    · simp only [if_pos hb]
      linarith [hT i]
    · simpa only [if_neg hb, zero_add] using hn i hb
  have hm := realUniformMean_mono T (fun i => (if bad i then 1 else 0) + u / 2) hp
  rw [realUniformMean_add, realUniformMean_const] at hm
  linarith

def cyclicPairShiftMap (q s : ℕ) (h h' : ℤ)
    (v : smoothingShiftLabels s × smoothingShiftLabels s) : ZMod q :=
  ((2 * h * v.1.val + 2 * h' * v.2.val : ℤ) : ZMod q)

theorem cyclicPairLocalSeven_le_one (q s : ℕ) [NeZero q]
    (H : ZMod q → ℂ) (hH : ∀ y, ‖H y‖ ≤ 1) (h h' : ℤ) :
    localCubeNorm 6 H (cyclicPairShiftMap q s h h') ≤ 1 :=
  localCubeNorm_le_one 6 H _ hH

theorem original_scale_parameter_bound (a : ℝ)
    (hβ : (a / 4) ^ 16 / (4 * 57 ^ 16) ≤ 1) : a ≤ 256 := by
  have hp : (a / 4) ^ 16 ≤ (64 : ℝ) ^ 16 := by
    have hden : (0 : ℝ) < 4 * 57 ^ 16 := by norm_num
    have hb := (div_le_iff₀ hden).mp hβ
    norm_num at hb ⊢
    linarith
  have ha := le_of_pow_le_pow_left₀ (by decide : (16 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 64) hp
  linarith



theorem shrunk_radius_short {N : ℕ} (hN : 0 < N) (a u : ℝ)
    (ha : 0 ≤ a) (ha256 : a ≤ 256) (hu : 0 < u) (hu8 : u < 1 / 8) :
    2 * ⌊u * smoothingRadius N a⌋₊ < N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓ : (smoothingRadius N a : ℝ) ≤ 4 * N := by
    have hf := Nat.floor_le (show 0 ≤ a * N / 64 by positivity)
    change (smoothingRadius N a : ℝ) ≤ a * N / 64 at hf
    nlinarith
  have hs := Nat.floor_le (show 0 ≤ u * (smoothingRadius N a : ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_left hℓ hu.le
  have he : (2 : ℝ) * (⌊u * (smoothingRadius N a : ℝ)⌋₊ : ℝ) < N := by nlinarith
  exact_mod_cast he

theorem nat_floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have ht := Nat.lt_floor_add_one x
  linarith

theorem shrunk_radius_lower {N : ℕ} (a u : ℝ) (hu : 0 < u)
    (hscale : 128 ≤ a * N) (huscale : 256 ≤ u * a * N) :
    a * N / 128 ≤ (smoothingRadius N a : ℝ) ∧
      u * a * N / 256 ≤ (⌊u * smoothingRadius N a⌋₊ : ℝ) := by
  have hℓ := nat_floor_ge_half (show 2 ≤ a * N / 64 by linarith)
  have he : a * N / 128 ≤ (smoothingRadius N a : ℝ) := by
    change a * N / 64 / 2 ≤ (smoothingRadius N a : ℝ) at hℓ
    linarith
  refine ⟨he, ?_⟩
  have hm := mul_le_mul_of_nonneg_left he hu.le
  have ht : 2 ≤ u * (smoothingRadius N a : ℝ) := by nlinarith
  have hs := nat_floor_ge_half ht
  nlinarith

theorem pair_shift_integer_bound {N s : ℕ} (hN : 0 < N) (hs : 2 * s < N)
    (h h' v v' : ℤ) (hh : 0 ≤ h ∧ h ≤ N) (hh' : 0 ≤ h' ∧ h' ≤ N)
    (hv : |v| ≤ s) (hv' : |v'| ≤ s) :
    |2 * h * v + 2 * h' * v'| < 2 * (N : ℤ) ^ 2 := by
  have hp := mul_le_mul hh.2 hv (abs_nonneg v) (Nat.cast_nonneg N : (0 : ℤ) ≤ N)
  have hp' := mul_le_mul hh'.2 hv' (abs_nonneg v') (Nat.cast_nonneg N : (0 : ℤ) ≤ N)
  have hn : (0 : ℤ) < N := by exact_mod_cast hN
  have hsr : (2 : ℤ) * s < N := by exact_mod_cast hs
  calc
    _ ≤ |2 * h * v| + |2 * h' * v'| := abs_add_le _ _
    _ = 2 * h * |v| + 2 * h' * |v'| := by
      simp only [abs_mul, abs_of_nonneg hh.1, abs_of_nonneg hh'.1, abs_of_pos (by norm_num : (0 : ℤ) < 2)]
    _ ≤ 4 * N * s := by nlinarith
    _ < _ := by nlinarith

theorem bounded_pair_values_no_wrap {N q : ℕ} (hq : 4 * N ^ 2 < q)
    (a b : ℤ) (ha : |a| < 2 * (N : ℤ) ^ 2) (hb : |b| < 2 * (N : ℤ) ^ 2)
    (he : (a : ZMod q) = (b : ZMod q)) : a = b := by
  have hcast : ((a + 2 * (N : ℤ) ^ 2 : ℤ) : ZMod q) =
      ((b + 2 * (N : ℤ) ^ 2 : ℤ) : ZMod q) := by
    push_cast
    rw [he]
  have hr := (ZMod.intCast_eq_intCast_iff' (a + 2 * (N : ℤ) ^ 2)
    (b + 2 * (N : ℤ) ^ 2) q).mp hcast
  have hqr : 4 * (N : ℤ) ^ 2 < q := by exact_mod_cast hq
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hr
  omega



theorem uniform_shrunk_radius_threshold (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      128 ≤ a * N ∧ 256 ≤ u * a * N := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (128 / a) (256 / (u * a)))
  refine ⟨B + 1, by omega, ?_⟩
  intro N hN
  have hBN : (B : ℝ) ≤ N := by exact_mod_cast (show B ≤ N by omega)
  have h₁ : 128 / a < N := (le_max_left _ _).trans_lt (hB.trans_le hBN)
  have h₂ : 256 / (u * a) < N := (le_max_right _ _).trans_lt (hB.trans_le hBN)
  constructor
  · have he := (div_lt_iff₀ ha).mp h₁
    nlinarith
  · have he := (div_lt_iff₀ (mul_pos hu ha)).mp h₂
    nlinarith

end GMZP0
