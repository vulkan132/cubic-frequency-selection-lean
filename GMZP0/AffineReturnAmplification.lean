import GMZP0.ReturnFiber

/-! Quantitative recurrence amplification through finitely many actual rounding fibers. -/

noncomputable section
namespace GMZP0

def returnRoundTargets (K : ℕ) : Finset ℤ := Finset.Icc (-(K : ℤ)) K

theorem card_returnRoundTargets (K : ℕ) : (returnRoundTargets K).card = 2 * K + 1 := by
  rw [returnRoundTargets, Int.card_Icc]
  have he : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, Int.toNat_natCast]

theorem rounded_affine_target_mem {N K : ℕ} (u v C : ℝ)
    (hu : |u| * (N : ℝ) ≤ C) (hv : |v| ≤ 1 / 2) (hK : C + 1 ≤ (K : ℝ))
    {h : ℤ} (hh : h ∈ Finset.Icc (-(N : ℤ)) N) :
    round (u * (h : ℝ) + v) ∈ returnRoundTargets K := by
  have hh' : |(h : ℝ)| ≤ (N : ℝ) := by
    have hz := Finset.mem_Icc.mp hh
    have hr : -(N : ℝ) ≤ (h : ℝ) ∧ (h : ℝ) ≤ N := by exact_mod_cast hz
    exact abs_le.mpr hr
  have hx : |u * (h : ℝ) + v| ≤ C + 1 / 2 := by
    calc
      _ ≤ |u| * |(h : ℝ)| + |v| := by simpa only [abs_mul] using abs_add_le (u * h) v
      _ ≤ |u| * (N : ℝ) + 1 / 2 := add_le_add (mul_le_mul_of_nonneg_left hh' (abs_nonneg _)) hv
      _ ≤ _ := by linarith
  have hr := abs_le.mp (abs_sub_round (u * (h : ℝ) + v))
  have hx' := abs_le.mp hx
  have hz : -(K : ℝ) ≤ (round (u * (h : ℝ) + v) : ℝ) ∧
      (round (u * (h : ℝ) + v) : ℝ) ≤ (K : ℝ) := by constructor <;> linarith
  apply Finset.mem_Icc.mpr
  exact_mod_cast hz

/-- No root is chosen when transferring the multiplied return to a real representative. -/
theorem multiplied_affine_return_lift (a b : Frequency) (q h : ℤ) (u v : ℝ)
    (hu : (u : Frequency) = q • a) (hv : (v : Frequency) = q • b) :
    ((u * (h : ℝ) + v : ℝ) : Frequency) = q • (h • a + b) := by
  have hh : (((h : ℝ) * u : ℝ) : Frequency) = h • (q • a) := by
    rw [← zsmul_eq_mul, AddCircle.coe_zsmul, hu]
  rw [mul_comm u, AddCircle.coe_add, hh, hv, smul_add, smul_comm h q a]

/-- Dense actual returns turn the small multiple into an error divided by their count. -/
theorem affine_return_amplification {N Q K : ℕ} (hQ : 0 < Q) (s : Finset ℤ)
    (hs : s ⊆ Finset.Icc (-(N : ℤ)) N) (hseed : 2 * N / Q + 1 < s.card)
    (hsize : 2 * (2 * K + 1) ≤ s.card) (a b : Frequency) {ε C : ℝ}
    (hε : 0 ≤ ε) (hscale : ε * (N : ℝ) ≤ C) (hK : 2 * C + 1 ≤ (K : ℝ))
    (hreturn : ∀ h ∈ s, ‖h • a + b‖ ≤ ε) :
    ∃ q : ℤ, 0 < q ∧ q < Q ∧
      ‖q • a‖ * (s.card : ℝ) ≤ 4 * (2 * (K : ℝ) + 1) * (Q : ℝ) * ε := by
  obtain ⟨q, hq0, hqQ, hq⟩ := affine_return_small_multiple hQ s hs hseed a b hreturn
  obtain ⟨u, hu, hunorm⟩ := exists_nearest_frequency_lift (q • a)
  obtain ⟨v, hv, hvnorm⟩ := exists_nearest_frequency_lift (q • b)
  have huN : |u| * (N : ℝ) ≤ 2 * C := by
    rw [hunorm]
    have hm := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith
  have hvhalf : |v| ≤ (1 : ℝ) / 2 := by
    rw [hvnorm]
    simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := q • b) one_ne_zero
  have hmaps : ∀ h ∈ s, round (u * (h : ℝ) + v) ∈ returnRoundTargets K :=
    fun h hh => rounded_affine_target_mem u v (2 * C) huN hvhalf hK (hs hh)
  have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq0.le
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ.le
  have hr : ∀ h ∈ s, |u * (h : ℝ) + v - (round (u * (h : ℝ) + v) : ℝ)| ≤ (Q : ℝ) * ε := by
    intro h hh
    rw [← UnitAddCircle.norm_eq, multiplied_affine_return_lift a b q h u v hu hv]
    calc
      ‖q • (h • a + b)‖ ≤ |(q : ℝ)| * ‖h • a + b‖ := norm_zsmul_le q _
      _ = (q : ℝ) * ‖h • a + b‖ := by rw [abs_of_nonneg hqR]
      _ ≤ (q : ℝ) * ε := mul_le_mul_of_nonneg_left (hreturn h hh) hqR
      _ ≤ (Q : ℝ) * ε := mul_le_mul_of_nonneg_right hqQR hε
  have hT : (returnRoundTargets K).Nonempty := ⟨0, by simp [returnRoundTargets]⟩
  have hsize' : 2 * (returnRoundTargets K).card ≤ s.card := by
    simpa only [card_returnRoundTargets] using hsize
  have hb := affine_slope_from_rounded_returns s (returnRoundTargets K) hT u v ((Q : ℝ) * ε)
    hmaps hr hsize'
  refine ⟨q, hq0, hqQ, ?_⟩
  simpa only [hunorm, card_returnRoundTargets, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_assoc] using hb

end GMZP0
