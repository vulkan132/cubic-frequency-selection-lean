import GMZP0.ParameterDensity

/-! Normalized density energy is controlled by the largest original representation multiplicity. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem parameterDensity_le_multiplicity {G A : Type*} [Fintype G] [Fintype A] [DecidableEq G]
    (r : A → G) (K : ℕ) (hK : ∀ x, (Finset.univ.filter (fun a => r a = x)).card ≤ K) (x : G) :
    parameterDensity r x ≤ (Fintype.card G : ℝ) * K / Fintype.card A := by
  rw [parameterDensity_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast hK x

theorem parameterDensity_energy_le {G A : Type*} [Fintype G] [Nonempty G] [Fintype A]
    [Nonempty A] [DecidableEq G] (r : A → G) (K : ℕ)
    (hK : ∀ x, (Finset.univ.filter (fun a => r a = x)).card ≤ K) :
    realUniformMean (fun x => parameterDensity r x ^ 2) ≤
      (Fintype.card G : ℝ) * K / Fintype.card A := by
  calc
    _ ≤ realUniformMean (fun x =>
        ((Fintype.card G : ℝ) * K / Fintype.card A) * parameterDensity r x) := by
      apply realUniformMean_mono
      intro x
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (parameterDensity_le_multiplicity r K hK x)
        (parameterDensity_nonneg r x)
    _ = _ := by rw [realUniformMean_const_mul, parameterDensity_mean_one, mul_one]

end GMZP0
