import GMZP0.BoxMoment

/-! The nonnegative box root, with its exact moment identity. -/

noncomputable section
namespace GMZP0

def iteratedSqrt : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.sqrt (iteratedSqrt n x)

theorem iteratedSqrt_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ iteratedSqrt n x := by
  cases n with
  | zero => exact hx
  | succ n => exact Real.sqrt_nonneg _

theorem iteratedSqrt_pow (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    iteratedSqrt n x ^ (2 ^ n) = x := by
  induction n with
  | zero => simp [iteratedSqrt]
  | succ n ih =>
    rw [iteratedSqrt, pow_succ', pow_mul, Real.sq_sqrt (iteratedSqrt_nonneg n x hx)]
    exact ih

def boxNorm {A : Type*} [Fintype A] (n : ℕ) (F : (Fin (n + 1) → A) → ℂ) : ℝ :=
  iteratedSqrt (n + 1) (boxMoment n F)

theorem boxNorm_nonneg {A : Type*} [Fintype A] (n : ℕ) (F : (Fin (n + 1) → A) → ℂ) :
    0 ≤ boxNorm n F := iteratedSqrt_nonneg _ _ (boxMoment_nonneg n F)

theorem boxNorm_pow {A : Type*} [Fintype A] (n : ℕ) (F : (Fin (n + 1) → A) → ℂ) :
    boxNorm n F ^ (2 ^ (n + 1)) = boxMoment n F :=
  iteratedSqrt_pow _ _ (boxMoment_nonneg n F)

theorem boxCorrelation_le_boxNorm {A : Type*} [Fintype A] [Nonempty A]
    (n : ℕ) (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ = 1) (hi : ∀ i, FaceIndependent (b i) i) :
    ‖boxCorrelation F b‖ ≤ boxNorm n F := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) (boxNorm_nonneg n F)
  rw [boxNorm_pow]
  exact box_cauchy_schwarz n F b hb hi

theorem boxNorm_le_one {A : Type*} [Fintype A] [Nonempty A]
    (n : ℕ) (F : (Fin (n + 1) → A) → ℂ) (hF : ∀ u, ‖F u‖ ≤ 1) : boxNorm n F ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero (n + 1) (by decide : (2 : ℕ) ≠ 0)) zero_le_one
  rw [boxNorm_pow, one_pow]
  exact boxMoment_le_one n F hF

end GMZP0
