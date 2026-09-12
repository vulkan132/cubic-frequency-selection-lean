import GMZP0.OrdinaryFreezing

/-! Elementary dense monomial amplification using actual same-sign rounding fibers. -/
noncomputable section
namespace GMZP0

/-- One actual sign has at least half the returns; reflection records original provenance. -/
theorem nonnegative_monomial_returns {N : ℕ} (D : ℕ) (a : Frequency) (ε : ℝ)
    (S : Finset ℤ) (hS : S ⊆ Finset.Icc (-(N : ℤ)) N)
    (hr : ∀ h ∈ S, ‖(h ^ D) • a‖ ≤ ε) :
    ∃ T : Finset ℤ, T ⊆ Finset.Icc 0 (N : ℤ) ∧ S.card ≤ 2 * T.card ∧
      (∀ h ∈ T, h ∈ S ∨ -h ∈ S) ∧ (∀ h ∈ T, ‖(h ^ D) • a‖ ≤ ε) := by
  classical
  let A := S.filter (fun h => 0 ≤ h)
  let B := S.filter (fun h => ¬ 0 ≤ h)
  have hsum : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
  by_cases ha : S.card ≤ 2 * A.card
  · refine ⟨A, ?_, ha, ?_, ?_⟩
    · intro h hh
      obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_Icc.mpr ⟨hp, (Finset.mem_Icc.mp (hS hs)).2⟩
    · intro h hh
      exact Or.inl (Finset.mem_filter.mp hh).1
    · intro h hh
      exact hr h (Finset.mem_filter.mp hh).1
  · let T := B.image (fun h => -h)
    have hcard : T.card = B.card := Finset.card_image_of_injective _ neg_injective
    refine ⟨T, ?_, by rw [hcard]; omega, ?_, ?_⟩
    · intro h hh
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨hs, hn⟩ := Finset.mem_filter.mp hk
      have hki := Finset.mem_Icc.mp (hS hs)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro h hh
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
      exact Or.inr (by simpa only [neg_neg] using (Finset.mem_filter.mp hk).1)
    · intro h hh
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
      have he := ordinary_power_return_reverse a D 1 k
      simp only [one_smul] at he
      rw [he]
      exact hr k (Finset.mem_filter.mp hk).1

/-- A macroscopic same-sign integer gap gives the full power gain without a derivative estimate. -/
theorem nonnegative_power_gap (D : ℕ) (hD : 1 ≤ D) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y - x) ^ D ≤ y ^ D - x ^ D := by
  have hp := pow_add_pow_le hx (sub_nonneg.mpr hxy) (by omega : D ≠ 0)
  rw [add_sub_cancel] at hp
  linarith

/-- Distinct nonnegative integers in one real rounding fiber control the monomial coefficient. -/
theorem monomial_fiber_spread (D : ℕ) (hD : 1 ≤ D) (S : Finset ℤ) (hS : S.Nonempty)
    (hpos : ∀ h ∈ S, 0 ≤ h) (u j ε : ℝ)
    (hr : ∀ h ∈ S, |u * (h : ℝ) ^ D - j| ≤ ε) :
    |u| * ((S.card : ℝ) - 1) ^ D ≤ 2 * ε := by
  have hdiam := integer_card_le_diameter S hS
  have hlo := hr _ (S.min'_mem hS)
  have hhi := hr _ (S.max'_mem hS)
  have hmn : (S.min' hS : ℝ) ≤ (S.max' hS : ℝ) := by
    exact_mod_cast S.min'_le _ (S.max'_mem hS)
  have hmin : (0 : ℝ) ≤ S.min' hS := by exact_mod_cast hpos _ (S.min'_mem hS)
  have hp := nonnegative_power_gap D hD (S.min' hS) (S.max' hS) hmin hmn
  have hc : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by
    have hc1 : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
    linarith
  have hd : |u| * ((S.max' hS : ℝ) ^ D - (S.min' hS : ℝ) ^ D) ≤ 2 * ε := by
    calc
      _ = |(u * (S.max' hS : ℝ) ^ D - j) - (u * (S.min' hS : ℝ) ^ D - j)| := by
        rw [show (u * (S.max' hS : ℝ) ^ D - j) - (u * (S.min' hS : ℝ) ^ D - j) =
          u * ((S.max' hS : ℝ) ^ D - (S.min' hS : ℝ) ^ D) by ring,
          abs_mul, abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hmin hmn D))]
      _ ≤ |u * (S.max' hS : ℝ) ^ D - j| + |u * (S.min' hS : ℝ) ^ D - j| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  exact (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hc hdiam D).trans hp) (abs_nonneg u)).trans hd

/-- Actual bounded rounding targets amplify a nonnegative monomial return by the full set diameter. -/
theorem monomial_from_rounded_returns (D : ℕ) (hD : 1 ≤ D) (S T : Finset ℤ) (hT : T.Nonempty)
    (hpos : ∀ h ∈ S, 0 ≤ h) (u ε : ℝ)
    (hmaps : ∀ h ∈ S, round (u * (h : ℝ) ^ D) ∈ T)
    (hr : ∀ h ∈ S, |u * (h : ℝ) ^ D - (round (u * (h : ℝ) ^ D) : ℝ)| ≤ ε)
    (hsize : 2 * T.card ≤ S.card) :
    |u| * ((S.card : ℝ) / (2 * T.card)) ^ D ≤ 2 * ε := by
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hSc : (0 : ℝ) < S.card := by
    have := Finset.card_pos.mpr hT
    exact_mod_cast (show 0 < S.card by omega)
  have hb : T.card • ((S.card : ℝ) / (T.card : ℝ)) ≤ (S.card : ℝ) := by
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hTc.ne']
  obtain ⟨j, _, hj⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hT hb
  let fiber : Finset ℤ := S.filter fun h => round (u * (h : ℝ) ^ D) = j
  have hj' : (S.card : ℝ) / (T.card : ℝ) ≤ (fiber.card : ℝ) := hj
  have hfc : 0 < fiber.card := by
    have : (0 : ℝ) < fiber.card := (div_pos hSc hTc).trans_le hj'
    exact_mod_cast this
  have hf := monomial_fiber_spread D hD fiber (Finset.card_pos.mp hfc)
    (fun h hh => hpos h (Finset.mem_filter.mp hh).1) u j ε (by
      intro h hh
      obtain ⟨hhS, hhj⟩ := Finset.mem_filter.mp hh
      simpa only [hhj] using hr h hhS)
  have hsizeR : 2 * (T.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hsize
  have hhalf : (S.card : ℝ) / (2 * T.card) ≤ (fiber.card : ℝ) - 1 := by
    have hcard := (div_le_iff₀ hTc).mp hj'
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T.card)).2
    nlinarith
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hhalf D) (abs_nonneg u)).trans hf

/-- The seed-scale bound keeps the actual nearest-integer targets in a fixed finite interval. -/
theorem rounded_monomial_target_mem {N K : ℕ} (D : ℕ) (u C : ℝ)
    (hu : |u| * (N : ℝ) ^ D ≤ C) (hK : C + 1 ≤ (K : ℝ))
    {h : ℤ} (hh : h ∈ Finset.Icc (0 : ℤ) N) :
    round (u * (h : ℝ) ^ D) ∈ returnRoundTargets K := by
  have hhR : (0 : ℝ) ≤ h ∧ (h : ℝ) ≤ N := by exact_mod_cast Finset.mem_Icc.mp hh
  have hx : |u * (h : ℝ) ^ D| ≤ C := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hhR.1 D)]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hhR.1 hhR.2 D) (abs_nonneg u)).trans hu
  have hr := abs_le.mp (abs_sub_round (u * (h : ℝ) ^ D))
  have hx' := abs_le.mp hx
  have hz : -(K : ℝ) ≤ (round (u * (h : ℝ) ^ D) : ℝ) ∧
      (round (u * (h : ℝ) ^ D) : ℝ) ≤ (K : ℝ) := by constructor <;> linarith
  apply Finset.mem_Icc.mpr
  exact_mod_cast hz

/-- A bounded small multiple is amplified using the actual dense return set, also when m=D.
All constants precede N, the circle coefficient, the set, and the seed's actual multiplier. -/
theorem uniform_monomial_amplification (D m : ℕ) (hD : 1 ≤ D) (hm : D ≤ m)
    (ρ C A : ℝ) (hρ : 0 < ρ) (hC : 0 < C) (hA : 0 < A) (Q : ℕ) (hQ : 0 < Q) :
    ∃ E : ℝ, ∃ N₀ : ℕ, 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a : Frequency, ∀ S : Finset ℤ,
        S ⊆ Finset.Icc (-(N : ℤ)) N → ρ * (N : ℝ) ≤ S.card →
        (∀ h ∈ S, ‖(h ^ D) • a‖ ≤ C / (N : ℝ) ^ m) →
        ∀ q : ℕ, 0 < q → q ≤ Q → ‖q • a‖ ≤ A / (N : ℝ) ^ m →
          ‖q • a‖ ≤ E / (N : ℝ) ^ (m + D) := by
  let K : ℕ := Nat.ceil (A + 1)
  let B : ℕ := 2 * K + 1
  let E : ℝ := 2 * (Q : ℝ) * C / (ρ / (4 * B)) ^ D
  let N₀ : ℕ := Nat.ceil (8 * (B : ℝ) / ρ) + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  refine ⟨E, N₀, by dsimp [E]; positivity, hN₀, ?_⟩
  intro N hN a S hS hd hr q hq hqQ hseed
  have hn : 0 < N := hN₀.trans_le hN
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have hlarge : 8 * (B : ℝ) ≤ (N : ℝ) * ρ := by
    have hceil : Nat.ceil (8 * (B : ℝ) / ρ) ≤ N := by dsimp [N₀] at hN; omega
    exact (div_le_iff₀ hρ).mp ((Nat.le_ceil _).trans (by exact_mod_cast hceil))
  obtain ⟨T, hT, hcard, _, hret⟩ := nonnegative_monomial_returns D a (C / (N : ℝ) ^ m) S hS hr
  have hhalf : ρ * (N : ℝ) / 2 ≤ T.card := by
    have hcR : (S.card : ℝ) ≤ 2 * (T.card : ℝ) := by exact_mod_cast hcard
    linarith
  have hsize : 2 * (returnRoundTargets K).card ≤ T.card := by
    rw [card_returnRoundTargets]
    have hh : 2 * (B : ℝ) ≤ T.card := by nlinarith
    exact_mod_cast hh
  obtain ⟨u, hu, hunorm⟩ := exists_nearest_frequency_lift (q • a)
  have huN : |u| * (N : ℝ) ^ D ≤ A := by
    rw [hunorm]
    have hp : (N : ℝ) ^ D ≤ (N : ℝ) ^ m := pow_le_pow_right₀ hn1 hm
    calc
      _ ≤ (A / (N : ℝ) ^ m) * (N : ℝ) ^ D :=
        mul_le_mul_of_nonneg_right hseed (by positivity)
      _ ≤ (A / (N : ℝ) ^ m) * (N : ℝ) ^ m := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = A := div_mul_cancel₀ _ (pow_ne_zero _ hnR.ne')
  have hmaps : ∀ h ∈ T, round (u * (h : ℝ) ^ D) ∈ returnRoundTargets K :=
    fun h hh => rounded_monomial_target_mem D u A huN (Nat.le_ceil _) (hT hh)
  have hround : ∀ h ∈ T, |u * (h : ℝ) ^ D - (round (u * (h : ℝ) ^ D) : ℝ)| ≤
      (Q : ℝ) * (C / (N : ℝ) ^ m) := by
    intro h hh
    have he : ((u * (h : ℝ) ^ D : ℝ) : Frequency) = q • ((h ^ D) • a) := by
      rw [mul_comm u, ← Int.cast_pow, ← zsmul_eq_mul, AddCircle.coe_zsmul, hu]
      module
    rw [← UnitAddCircle.norm_eq, he]
    exact norm_nsmul_le.trans ((mul_le_mul_of_nonneg_left (hret h hh) (Nat.cast_nonneg q)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (by positivity)))
  have htargets : (returnRoundTargets K).Nonempty := ⟨0, by simp [returnRoundTargets]⟩
  have hb := monomial_from_rounded_returns D hD T (returnRoundTargets K) htargets
    (fun h hh => (Finset.mem_Icc.mp (hT hh)).1) u ((Q : ℝ) * (C / (N : ℝ) ^ m)) hmaps hround hsize
  have hgain : (ρ / (4 * B)) * (N : ℝ) ≤ (T.card : ℝ) / (2 * (returnRoundTargets K).card) := by
    rw [card_returnRoundTargets]
    change _ ≤ (T.card : ℝ) / (2 * (B : ℝ))
    calc
      _ = (ρ * (N : ℝ) / 2) / (2 * B) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hhalf (by positivity)
  have hb' := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hgain D) (abs_nonneg u)).trans hb
  have hx : |u| * (ρ / (4 * B)) ^ D * (N : ℝ) ^ D ≤
      (2 * (Q : ℝ) * C) / (N : ℝ) ^ m := by
    simpa only [mul_pow, ← mul_assoc, mul_div_assoc] using hb'
  rw [← hunorm]
  apply (le_div_iff₀ (pow_pos hnR _)).2
  dsimp only [E]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (ρ / (4 * B)) ^ D)).2
  have hx' := (le_div_iff₀ (pow_pos hnR m)).mp hx
  rw [pow_add]
  convert hx' using 1
  ring

end GMZP0
