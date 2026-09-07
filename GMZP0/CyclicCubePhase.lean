import GMZP0.CyclicCubeReroot
import GMZP0.CubePhaseAlgebra

/-! Sixteen original weight factors, alternating alignments, and the exact t-cubic coefficient. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def cyclicCubeWeight (N q ℓ : ℕ) (σ : Base N → ℝ) (x : Fin N) (Y : ZMod q)
    (h : ℤ) (u : CubeShiftPairs ℓ) : ℝ :=
  ∏ ω : Fin 4 → Bool, cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω)

def cyclicCubeAlignment (N q ℓ : ℕ) (lam : Base N → ℂ) (x : Fin N) (Y : ZMod q)
    (h : ℤ) (u : CubeShiftPairs ℓ) : ℂ :=
  ∏ ω : Fin 4 → Bool, cubeConj 4 ω (conj (cyclicField N q lam 1 x (cyclicCubeVertex q ℓ h Y u ω)))

def cyclicCubePhase (N q ℓ : ℕ) (p : Base N → Frequency) (x : Fin N) (Y : ZMod q)
    (h k : ℤ) (u : CubeShiftPairs ℓ) (t : ℤ) : Frequency :=
  ∑ ω : Fin 4 → Bool, cubeSign 4 ω •
    (-((t + h - k - cubeShiftSum ℓ u ω) ^ 3 • cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω)))

/-- This coefficient has no t or k argument. -/
def cyclicCubeCubicCoeff (N q ℓ : ℕ) (p : Base N → Frequency) (x : Fin N) (Y : ZMod q)
    (h : ℤ) (u : CubeShiftPairs ℓ) : Frequency :=
  -(∑ ω : Fin 4 → Bool, cubeSign 4 ω • cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω))

def cyclicCubeCoefficients (N q ℓ : ℕ) (p : Base N → Frequency) (x : Fin N) (Y : ZMod q)
    (h k : ℤ) (u : CubeShiftPairs ℓ) : Fin 4 → Frequency :=
  let e := cubeSign 4
  let d := fun ω => h - k - cubeShiftSum ℓ u ω
  let a := fun ω => cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω)
  ![∑ ω, (-e ω * d ω ^ 3) • a ω,
    ∑ ω, (-3 * e ω * d ω ^ 2) • a ω,
    ∑ ω, (-3 * e ω * d ω) • a ω,
    cyclicCubeCubicCoeff N q ℓ p x Y h u]

theorem cyclicRerootedCubeProduct_factorized (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (x : Fin N) (Y : ZMod q)
    (h t k : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicRerootedCubeProduct N q ℓ p σ lam x Y h t k u =
      (cyclicCubeWeight N q ℓ σ x Y h u : ℂ) * cyclicCubeAlignment N q ℓ lam x Y h u *
        circleCharacter (cyclicCubePhase N q ℓ p x Y h k u t) := by
  exact alternating_weighted_character_product 4
    (fun ω => cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω))
    (fun ω => cyclicField N q lam 1 x (cyclicCubeVertex q ℓ h Y u ω))
    (fun ω => -((t + h - k - cubeShiftSum ℓ u ω) ^ 3 •
      cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω)))

theorem cyclicCubePhase_polynomial (N q ℓ : ℕ) (p : Base N → Frequency)
    (x : Fin N) (Y : ZMod q) (h k t : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubePhase N q ℓ p x Y h k u t =
      t ^ 3 • cyclicCubeCoefficients N q ℓ p x Y h k u 3 +
      t ^ 2 • cyclicCubeCoefficients N q ℓ p x Y h k u 2 +
      t • cyclicCubeCoefficients N q ℓ p x Y h k u 1 +
      cyclicCubeCoefficients N q ℓ p x Y h k u 0 := by
  simpa [cyclicCubePhase, cyclicCubeCoefficients, cyclicCubeCubicCoeff,
    neg_zsmul, Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc] using
    circle_cubic_sum (cubeSign 4) (fun ω => h - k - cubeShiftSum ℓ u ω)
      (fun ω => cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω)) t

theorem cyclicCubeCoefficients_top (N q ℓ : ℕ) (p : Base N → Frequency)
    (x : Fin N) (Y : ZMod q) (h k : ℤ) (u : CubeShiftPairs ℓ) :
    cyclicCubeCoefficients N q ℓ p x Y h k u 3 = cyclicCubeCubicCoeff N q ℓ p x Y h u := by
  simp [cyclicCubeCoefficients]

theorem cyclicCubeWeight_bounds (N q ℓ : ℕ) (σ : Base N → ℝ) (x : Fin N) (Y : ZMod q)
    (h : ℤ) (u : CubeShiftPairs ℓ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) :
    0 ≤ cyclicCubeWeight N q ℓ σ x Y h u ∧ cyclicCubeWeight N q ℓ σ x Y h u ≤ 1 := by
  have hw (ω : Fin 4 → Bool) :
      0 ≤ cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω) ∧
        cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω) ≤ 1 :=
    cyclicField_property N q σ 0 (fun a : ℝ => 0 ≤ a ∧ a ≤ 1) hσ ⟨le_rfl, zero_le_one⟩ _ _
  exact ⟨Finset.prod_nonneg (fun ω _ => (hw ω).1),
    Finset.prod_le_one (fun ω _ => (hw ω).1) (fun ω _ => (hw ω).2)⟩

theorem cyclicCubeAlignment_norm (N q ℓ : ℕ) (lam : Base N → ℂ) (x : Fin N) (Y : ZMod q)
    (h : ℤ) (u : CubeShiftPairs ℓ) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖cyclicCubeAlignment N q ℓ lam x Y h u‖ = 1 := by
  simp only [cyclicCubeAlignment, norm_prod, cubeConj_norm, Complex.norm_conj]
  apply Finset.prod_eq_one
  intro ω _
  exact cyclicField_property N q lam 1 (fun a : ℂ => ‖a‖ = 1) hlam (by simp) _ _

theorem cyclicRerootedCubeProduct_norm (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (x : Fin N) (Y : ZMod q)
    (h t k : ℤ) (u : CubeShiftPairs ℓ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖cyclicRerootedCubeProduct N q ℓ p σ lam x Y h t k u‖ = cyclicCubeWeight N q ℓ σ x Y h u := by
  rw [cyclicRerootedCubeProduct_factorized, norm_mul, norm_mul, norm_circleCharacter,
    cyclicCubeAlignment_norm N q ℓ lam x Y h u hlam, mul_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cyclicCubeWeight_bounds N q ℓ σ x Y h u hσ).1]

end GMZP0
