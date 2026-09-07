import GMZP0.PhaseScale

/-! Exact circle-valued phase algebra, without choosing real lifts or root branches. -/

noncomputable section
open scoped ComplexConjugate
namespace GMZP0

def circleCharacter (a : Frequency) : ℂ := (a.toCircle : ℂ)

def integerCubicPhase (a : Frequency) (r : ℤ) : ℂ := circleCharacter (r ^ 3 • a)

theorem circleCharacter_add (a b : Frequency) :
    circleCharacter (a + b) = circleCharacter a * circleCharacter b := by
  simp only [circleCharacter, AddCircle.toCircle_add, Circle.coe_mul]

theorem circleCharacter_neg (a : Frequency) :
    circleCharacter (-a) = conj (circleCharacter a) := by
  simp only [circleCharacter, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

theorem circleCharacter_sub (a b : Frequency) :
    circleCharacter (a - b) = circleCharacter a * conj (circleCharacter b) := by
  rw [sub_eq_add_neg, circleCharacter_add, circleCharacter_neg]

theorem circleCharacter_real (a : ℝ) :
    circleCharacter (a : Frequency) = Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  simp only [circleCharacter, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]

theorem cubicPhase_integer {N : ℕ} (a : Frequency) (r : Fin N) :
    cubicPhase a r = integerCubicPhase a (label r) := by
  unfold cubicPhase integerCubicPhase circleCharacter
  rw [← Nat.cast_pow, natCast_zsmul]

def doublePhaseCoefficient (a b c : Frequency) (h k r : ℤ) : Frequency :=
  (r + k) ^ 3 • a - r ^ 3 • b - ((r + k - h) ^ 3 - (r - h) ^ 3) • c

/-- The original four phase factors combine into the manuscript's double phase on R/Z. -/
theorem double_phase_character (a b c : Frequency) (h k r : ℤ) :
    (integerCubicPhase a (r + k) * conj (integerCubicPhase c (r + k - h))) *
      conj (integerCubicPhase b r * conj (integerCubicPhase c (r - h))) =
        circleCharacter (doublePhaseCoefficient a b c h k r) := by
  simp only [integerCubicPhase, doublePhaseCoefficient, sub_zsmul, circleCharacter_sub,
    circleCharacter_add, circleCharacter_neg, map_mul, starRingEnd_self_apply]
  ring

/-- Rerooting r=t-k+h preserves all three distinct original frequency values. -/
theorem doublePhaseCoefficient_reroot (a b c : Frequency) (h k t : ℤ) :
    doublePhaseCoefficient a b c h k (t - k + h) =
      (t + h) ^ 3 • a - (t + h - k) ^ 3 • b - (t ^ 3 - (t - k) ^ 3) • c := by
  have h1 : t - k + h + k = t + h := by ring
  have h2 : t - k + h = t + h - k := by ring
  have h3 : t - k + h + k - h = t := by ring
  have h4 : t - k + h - h = t - k := by ring
  rw [doublePhaseCoefficient, h3, h4, h1, h2]

end GMZP0
