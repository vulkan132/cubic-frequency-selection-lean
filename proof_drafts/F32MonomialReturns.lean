import GMZP0.MonomialSeed
import GMZP0.MonomialAmplification

/-! The complete internal dense monomial return proof and its ordinary-freezing consequence. -/
noncomputable section
namespace GMZP0

/-- Dense monomial returns, including m=D, with no unproved core or external premise.
The original retained integer set, circle coefficient, positive multipliers and N scale are preserved. -/
theorem monomial_dense_returns : MonomialDenseReturns := by
  intro D m hD hm ρ C hρ hC
  obtain ⟨Q, N₁, hQ, hN₁, hseed⟩ := uniform_monomial_seed D ρ hρ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨E, N₂, hE, hN₂, hamp⟩ := uniform_monomial_amplification D m hD hm
    ρ C ((Q : ℝ) * C) hρ hC (by positivity) Q hQ
  refine ⟨Q, E, max N₁ N₂, hQ, hE, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN a S hS _ hd hr
  obtain ⟨q, hq, hqQ, hqa⟩ := hseed N ((le_max_left _ _).trans hN) a (C / (N : ℝ) ^ m)
    (by positivity) S hS hd hr
  refine ⟨q, hq, hqQ, ?_⟩
  apply hamp N ((le_max_right _ _).trans hN) a S hS hd hr q hq hqQ
  simpa only [mul_div_assoc] using hqa

/-- Complete ordinary polynomial freezing now has only the two explicit external Weyl premises.
No internal monomial-return, child-existence or degree-induction premise remains. -/
theorem uniform_ordinary_freezing_of_weyl (hW₀ : CubicTwoCoefficientWeylInput)
    (hW : PolynomialLeadingWeylInput) (D : ℕ) : UniformOrdinaryFreezing D :=
  uniform_ordinary_freezing_of_returns hW₀ hW monomial_dense_returns D

end GMZP0
