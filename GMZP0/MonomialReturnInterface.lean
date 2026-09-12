import GMZP0.PowerAffineReturns

/-! The exact nonlinear return statement and its checked denominator-fiber adapter.
F31 isolated this internal core obligation; MonomialReturns proves it at F32.
The witness is an actual theorem, not an external deep-theorem premise. -/
noncomputable section
namespace GMZP0

/-- Exact dense monomial return statement from the manuscript, including the critical m=D case.
All constants precede N, the original circle coefficient and the actual retained integer set. -/
def MonomialDenseReturns : Prop :=
  ∀ D m : ℕ, 1 ≤ D → D ≤ m → ∀ ρ C : ℝ, 0 < ρ → 0 < C →
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a : Frequency, ∀ S : Finset ℤ,
        S ⊆ Finset.Icc (-(N : ℤ)) N → (∀ h ∈ S, h ≠ 0) → ρ * (N : ℝ) ≤ S.card →
        (∀ h ∈ S, ‖(h ^ D) • a‖ ≤ C / (N : ℝ) ^ m) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ (m + D)

/-- The degree-one instance needs no unproved monomial-return premise. -/
theorem uniform_degree_one_monomial_returns (m : ℕ) (hm : 1 ≤ m)
    (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 < C) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a : Frequency, ∀ S : Finset ℤ,
        S ⊆ Finset.Icc (-(N : ℤ)) N → ρ * (N : ℝ) ≤ S.card →
        (∀ h ∈ S, ‖(h ^ 1) • a‖ ≤ C / (N : ℝ) ^ m) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ (m + 1) := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hr⟩ := uniform_affine_power_returns ρ C hρ hC
  refine ⟨Q, E, N₀, hQ, hE, hN₀, ?_⟩
  intro N hN a S hS hd hp
  exact hr m hm N hN a 0 S hS hd (by simpa only [pow_one, add_zero] using hp)

/-- Actual bounded multipliers are pigeonholed, preserving the same monomial and its full scale.
The modular adapter takes hR explicitly; MonomialReturns supplies its proved witness. -/
theorem uniform_bounded_multiplier_monomial_returns (hR : MonomialDenseReturns)
    (D m : ℕ) (hD : 1 ≤ D) (hm : D ≤ m) (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 < C)
    (B : ℕ) (hB : 0 < B) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a : Frequency, ∀ S : Finset ℤ,
        S ⊆ Finset.Icc (-(N : ℤ)) N → (∀ h ∈ S, h ≠ 0) → ρ * (N : ℝ) ≤ S.card →
        (∀ h ∈ S, ∃ b : ℕ, 0 < b ∧ b ≤ B ∧ ‖b • ((h ^ D) • a)‖ ≤ C / (N : ℝ) ^ m) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ (m + D) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hr⟩ := hR D m hD hm (ρ / B) C (by positivity) hC
  refine ⟨Q * B, E, N₀, by positivity, hE, hN₀, ?_⟩
  intro N hN a S hS hnonzero hd hp
  obtain ⟨b, hb0, hbB, T, hTS, hcard, ht⟩ := finite_positive_denominator_fiber hB S
    (fun h b => ‖b • ((h ^ D) • a)‖ ≤ C / (N : ℝ) ^ m) hp
  have hden : (ρ / B) * (N : ℝ) ≤ T.card := by
    calc
      _ = (ρ * N) / B := by ring
      _ ≤ (S.card : ℝ) / B := div_le_div_of_nonneg_right hd hBR.le
      _ ≤ _ := hcard
  have hret : ∀ h ∈ T, ‖(h ^ D) • (b • a)‖ ≤ C / (N : ℝ) ^ m := by
    intro h hh
    have he : (h ^ D) • (b • a) = b • ((h ^ D) • a) := by module
    rw [he]
    exact ht h hh
  obtain ⟨q, hq, hqQ, hb⟩ := hr N hN (b • a) T (hTS.trans hS)
    (fun h hh => hnonzero h (hTS hh)) hden hret
  have he : (q * b) • a = q • (b • a) := by module
  exact ⟨q * b, by positivity, Nat.mul_le_mul hqQ hbB, by simpa only [he] using hb⟩

end GMZP0
