import GMZP0.BoxMoment
import GMZP0.CircleCharacter

/-! Boolean parity, alternating conjugation, and signed circle characters. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def cubeConj : (d : ℕ) → (Fin d → Bool) → ℂ → ℂ
  | 0, _, z => z
  | d + 1, ω, z => if ω 0 then conj (cubeConj d (Fin.tail ω) z) else cubeConj d (Fin.tail ω) z

def cubeSign : (d : ℕ) → (Fin d → Bool) → ℤ
  | 0, _ => 1
  | d + 1, ω => if ω 0 then -cubeSign d (Fin.tail ω) else cubeSign d (Fin.tail ω)

theorem cubeConj_mul (d : ℕ) : ∀ (ω : Fin d → Bool) (z w : ℂ),
    cubeConj d ω (z * w) = cubeConj d ω z * cubeConj d ω w := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro ω z w
    simp only [cubeConj, ih]
    split <;> simp [map_mul]

theorem cubeConj_conj (d : ℕ) : ∀ (ω : Fin d → Bool) (z : ℂ),
    cubeConj d ω (conj z) = conj (cubeConj d ω z) := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro ω z
    simp only [cubeConj, ih]
    split <;> rfl

theorem cubeConj_ofReal (d : ℕ) : ∀ (ω : Fin d → Bool) (x : ℝ), cubeConj d ω (x : ℂ) = x := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro ω x
    simp only [cubeConj, ih, Complex.conj_ofReal, ite_self]

theorem cubeConj_norm (d : ℕ) : ∀ (ω : Fin d → Bool) (z : ℂ), ‖cubeConj d ω z‖ = ‖z‖ := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro ω z
    simp only [cubeConj]
    split <;> simp only [Complex.norm_conj, ih]

theorem cubeSign_eq_parity (d : ℕ) : ∀ ω : Fin d → Bool,
    cubeSign d ω = (-1 : ℤ) ^ (∑ i : Fin d, (ω i).toNat) := by
  induction d with
  | zero => intro ω; simp [cubeSign]
  | succ d ih =>
    intro ω
    simp only [cubeSign, Fin.sum_univ_succ, ih, Fin.tail]
    cases ω 0 <;> simp [pow_add]

theorem cubeConj_character (d : ℕ) : ∀ (ω : Fin d → Bool) (a : Frequency),
    cubeConj d ω (circleCharacter a) = circleCharacter (cubeSign d ω • a) := by
  induction d with
  | zero => intro ω a; simp [cubeConj, cubeSign]
  | succ d ih =>
    intro ω a
    simp only [cubeConj, cubeSign, ih]
    cases ω 0 <;> simp only [Bool.false_eq_true, if_false, if_true]
    rw [neg_zsmul, circleCharacter_neg]

theorem card_booleanVertices (d : ℕ) : Fintype.card (Fin d → Bool) = 2 ^ d := by
  simp

end GMZP0
