import GMZP0.FiniteSchur

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The finite square-root energy obeys the triangle inequality with constant one. -/
theorem finiteEnergy_sqrt_triangle {Z : Type*} [Fintype Z] (a b : Z → ℂ) :
    Real.sqrt (finiteEnergy (fun z => a z + b z)) ≤
      Real.sqrt (finiteEnergy a) + Real.sqrt (finiteEnergy b) := by
  have hp (z : Z) : ‖a z + b z‖ ^ 2 ≤ ‖a z‖ ^ 2 + ‖b z‖ ^ 2 + 2 * (‖a z‖ * ‖b z‖) := by
    have h := pow_le_pow_left₀ (norm_nonneg (a z + b z)) (norm_add_le (a z) (b z)) 2
    nlinarith
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset Z)) => hp z)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun z => ‖a z‖) (fun z => ‖b z‖)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change finiteEnergy (fun z => a z + b z) ≤ finiteEnergy a + finiteEnergy b +
    2 * ∑ z, ‖a z‖ * ‖b z‖ at hsum
  change (∑ z, ‖a z‖ * ‖b z‖) ≤ Real.sqrt (finiteEnergy a) * Real.sqrt (finiteEnergy b) at hcs
  have ha := Real.sq_sqrt (finiteEnergy_nonneg a)
  have hb := Real.sq_sqrt (finiteEnergy_nonneg b)
  have hab := Real.sq_sqrt (finiteEnergy_nonneg (fun z => a z + b z))
  have hna := Real.sqrt_nonneg (finiteEnergy a)
  have hnb := Real.sqrt_nonneg (finiteEnergy b)
  have hnab := Real.sqrt_nonneg (finiteEnergy (fun z => a z + b z))
  nlinarith

/-- Two supplied operator-energy bounds add at the norm level, without an extra factor two. -/
theorem finiteEnergy_add_bound {Z : Type*} [Fintype Z] (a b : Z → ℂ)
    (E α β : ℝ) (hE : 0 ≤ E) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : finiteEnergy a ≤ α ^ 2 * E) (hb : finiteEnergy b ≤ β ^ 2 * E) :
    finiteEnergy (fun z => a z + b z) ≤ (α + β) ^ 2 * E := by
  have hsa : Real.sqrt (finiteEnergy a) ≤ α * Real.sqrt E := by
    simpa only [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα] using Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt (finiteEnergy b) ≤ β * Real.sqrt E := by
    simpa only [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ] using Real.sqrt_le_sqrt hb
  have hab := finiteEnergy_sqrt_triangle a b
  have h : Real.sqrt (finiteEnergy (fun z => a z + b z)) ≤ (α + β) * Real.sqrt E := by
    nlinarith
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  simpa only [Real.sq_sqrt (finiteEnergy_nonneg _), mul_pow, Real.sq_sqrt hE] using hs

/-- The manuscript's three final pieces fit inside the requested squared error budget. -/
theorem finiteEnergy_three_piece_budget {Z : Type*} [Fintype Z] (a b c : Z → ℂ)
    (E s : ℝ) (hE : 0 ≤ E) (hs : 0 ≤ s)
    (ha : finiteEnergy a ≤ (s / 3) ^ 2 * E)
    (hb : finiteEnergy b ≤ (s / 12) ^ 2 * E)
    (hc : finiteEnergy c ≤ (s / 3) ^ 2 * E) :
    finiteEnergy (fun z => a z + b z + c z) ≤ s ^ 2 * E := by
  have hab := finiteEnergy_add_bound a b E (s / 3) (s / 12) hE (by positivity) (by positivity) ha hb
  have h := finiteEnergy_add_bound (fun z => a z + b z) c E (s / 3 + s / 12) (s / 3)
    hE (by positivity) (by positivity) hab hc
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hE
  nlinarith [sq_nonneg s]

end GMZP0
