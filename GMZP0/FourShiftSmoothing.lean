import GMZP0.FiniteAverages

/-! Four independent integer shifts, averaged over the full Cartesian product. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def smoothingShiftLabels (ℓ : ℕ) : Finset ℤ := Finset.Icc (-(ℓ : ℤ)) ℓ

abbrev FourShiftSpace (ℓ : ℕ) := Fin 4 → smoothingShiftLabels ℓ

instance smoothingShiftLabels_nonempty (ℓ : ℕ) : Nonempty (smoothingShiftLabels ℓ) :=
  ⟨⟨0, by simp [smoothingShiftLabels]⟩⟩

def fourShiftSum (ℓ : ℕ) (u : FourShiftSpace ℓ) : ℤ := ∑ i : Fin 4, (u i).val

theorem card_smoothingShiftLabels (ℓ : ℕ) : (smoothingShiftLabels ℓ).card = 2 * ℓ + 1 := by
  rw [smoothingShiftLabels, Int.card_Icc]
  omega

theorem card_fourShiftSpace (ℓ : ℕ) : Fintype.card (FourShiftSpace ℓ) = (2 * ℓ + 1) ^ 4 := by
  simp only [FourShiftSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    card_smoothingShiftLabels]

theorem fourShiftSum_abs_le (ℓ : ℕ) (u : FourShiftSpace ℓ) :
    |(fourShiftSum ℓ u : ℝ)| ≤ 4 * (ℓ : ℝ) := by
  have hi (i : Fin 4) : |((u i).val : ℝ)| ≤ (ℓ : ℝ) := by
    have hb := (u i).property
    simp only [smoothingShiftLabels, Finset.mem_Icc] at hb
    exact_mod_cast abs_le.mpr hb
  unfold fourShiftSum
  rw [Int.cast_sum]
  calc
    |∑ i : Fin 4, ((u i).val : ℝ)| ≤ ∑ i : Fin 4, |((u i).val : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, (ℓ : ℝ) := Finset.sum_le_sum fun i _ => hi i
    _ = 4 * (ℓ : ℝ) := by simp

def fourShiftSmoothedAverage (N ℓ : ℕ) (h t : ℤ) (f : ℤ → ℂ) : ℂ :=
  (∑ k ∈ lagInnerInterval N h t,
    complexUniformMean (fun u : FourShiftSpace ℓ => f (k + fourShiftSum ℓ u))) / (N : ℂ)

theorem fourShiftSmoothedAverage_eq (N ℓ : ℕ) (h t : ℤ) (f : ℤ → ℂ) :
    fourShiftSmoothedAverage N ℓ h t f =
      complexUniformMean (fun u : FourShiftSpace ℓ =>
        (∑ k ∈ lagInnerInterval N h t, f (k + fourShiftSum ℓ u)) / (N : ℂ)) := by
  exact (complexUniformMean_sum_div _ _ _).symm

theorem norm_fourShiftSmoothedAverage_sub_le {N : ℕ} (hN : 0 < N) (ℓ : ℕ)
    (h t : ℤ) (f : ℤ → ℂ) (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖fourShiftSmoothedAverage N ℓ h t f -
      (∑ k ∈ lagInnerInterval N h t, f k) / (N : ℂ)‖ ≤ 8 * (ℓ : ℝ) / N := by
  rw [fourShiftSmoothedAverage_eq]
  apply norm_complexUniformMean_sub_le
  intro u
  exact (norm_lag_sum_translate hN h t (fourShiftSum ℓ u) f hf).trans
    (div_le_div_of_nonneg_right (by nlinarith only [fourShiftSum_abs_le ℓ u])
      (Nat.cast_nonneg N))

def smoothingRadius (N : ℕ) (a : ℝ) : ℕ := ⌊a * N / 64⌋₊

theorem smoothingRadius_error {N : ℕ} (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) :
    8 * (smoothingRadius N a : ℝ) / N ≤ a / 8 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hf := Nat.floor_le (show 0 ≤ a * (N : ℝ) / 64 by positivity)
  rw [div_le_iff₀ hn]
  dsimp only [smoothingRadius]
  nlinarith only [hf]

end GMZP0
