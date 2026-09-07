import GMZP0.AffineReturnSeed
import Mathlib.Combinatorics.Pigeonhole

/-! Integer diameter and finite-fiber bounds for quantitative affine recurrence. -/

noncomputable section
namespace GMZP0

theorem integer_card_le_diameter (s : Finset ℤ) (hs : s.Nonempty) :
    (s.card : ℝ) - 1 ≤ (s.max' hs : ℝ) - (s.min' hs : ℝ) := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hc := Finset.card_le_card hsub
  have hmn : s.min' hs ≤ s.max' hs := s.min'_le _ (s.max'_mem hs)
  have hi := Int.card_Icc_of_le (s.min' hs) (s.max' hs) (show s.min' hs ≤ s.max' hs + 1 by omega)
  have hz : (s.card : ℤ) ≤ s.max' hs + 1 - s.min' hs := by
    calc
      (s.card : ℤ) ≤ (Finset.Icc (s.min' hs) (s.max' hs)).card := by exact_mod_cast hc
      _ = _ := hi
  have hr : (s.card : ℝ) ≤ (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by exact_mod_cast hz
  linarith

/-- All points in one rounding fiber share the same actual integer target. -/
theorem affine_fiber_spread (s : Finset ℤ) (hs : s.Nonempty)
    (u v j ε : ℝ) (hreturn : ∀ h ∈ s, |u * (h : ℝ) + v - j| ≤ ε) :
    ((s.card : ℝ) - 1) * |u| ≤ 2 * ε := by
  have hdiam := integer_card_le_diameter s hs
  have hleft := hreturn _ (s.min'_mem hs)
  have hright := hreturn _ (s.max'_mem hs)
  have hmn : (s.min' hs : ℝ) ≤ (s.max' hs : ℝ) := by
    exact_mod_cast s.min'_le _ (s.max'_mem hs)
  have hdiff : |u| * ((s.max' hs : ℝ) - (s.min' hs : ℝ)) ≤ 2 * ε := by
    calc
      _ = |(u * (s.max' hs : ℝ) + v - j) - (u * (s.min' hs : ℝ) + v - j)| := by
        rw [show (u * (s.max' hs : ℝ) + v - j) - (u * (s.min' hs : ℝ) + v - j) =
          u * ((s.max' hs : ℝ) - (s.min' hs : ℝ)) by ring,
          abs_mul, abs_of_nonneg (sub_nonneg.mpr hmn)]
      _ ≤ |u * (s.max' hs : ℝ) + v - j| + |u * (s.min' hs : ℝ) + v - j| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (u * (s.max' hs : ℝ) + v - j) 0 (u * (s.min' hs : ℝ) + v - j)
      _ ≤ 2 * ε := by linarith
  exact (mul_le_mul_of_nonneg_right hdiam (abs_nonneg u)).trans (by nlinarith [hdiff])

/-- A finite number of possible rounding integers improves the slope by the set's size. -/
theorem affine_slope_from_rounded_returns (s T : Finset ℤ) (hT : T.Nonempty)
    (u v ε : ℝ)
    (hmaps : ∀ h ∈ s, round (u * (h : ℝ) + v) ∈ T)
    (hreturn : ∀ h ∈ s, |u * (h : ℝ) + v - (round (u * (h : ℝ) + v) : ℝ)| ≤ ε)
    (hsize : 2 * T.card ≤ s.card) :
    |u| * (s.card : ℝ) ≤ 4 * (T.card : ℝ) * ε := by
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hSc : (0 : ℝ) < s.card := by
    have := Finset.card_pos.mpr hT
    exact_mod_cast (show 0 < s.card by omega)
  have hb : T.card • ((s.card : ℝ) / (T.card : ℝ)) ≤ (s.card : ℝ) := by
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hTc.ne']
  obtain ⟨j, _, hj⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hT hb
  let fiber : Finset ℤ := s.filter fun h : ℤ => round (u * (h : ℝ) + v) = j
  have hj' : (s.card : ℝ) / (T.card : ℝ) ≤ (fiber.card : ℝ) := hj
  have hfc : 0 < fiber.card := by
    have : (0 : ℝ) < fiber.card := (div_pos hSc hTc).trans_le hj'
    exact_mod_cast this
  have hf := affine_fiber_spread fiber (Finset.card_pos.mp hfc) u v j ε (by
    intro h hh
    obtain ⟨hhS, hhj⟩ := Finset.mem_filter.mp hh
    simpa only [hhj] using hreturn h hhS)
  have hcard := (div_le_iff₀ hTc).mp hj'
  have hsizeR : 2 * (T.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hsize
  have h1 := mul_le_mul_of_nonneg_left hcard (abs_nonneg u)
  have h2 := mul_le_mul_of_nonneg_left hf hTc.le
  have h3 := mul_le_mul_of_nonneg_right hsizeR (abs_nonneg u)
  nlinarith

end GMZP0
