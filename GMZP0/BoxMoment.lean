import GMZP0.BoxFaces

/-! Nonnegative box moments and the full iterated face Cauchy–Schwarz inequality. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- The (n+1)-dimensional box moment, with all coordinate pairs averaged uniformly. -/
def boxMoment {A : Type*} [Fintype A] : (n : ℕ) → ((Fin (n + 1) → A) → ℂ) → ℝ
  | 0, F => ‖complexUniformMean F‖ ^ 2
  | n + 1, F => realUniformMean (fun z : A × A => boxMoment n (boxDoubledFunction F z))

theorem boxMoment_nonneg {A : Type*} [Fintype A] (n : ℕ) :
    ∀ F : (Fin (n + 1) → A) → ℂ, 0 ≤ boxMoment n F := by
  induction n with
  | zero => intro F; exact sq_nonneg _
  | succ n ih =>
    intro F
    exact realUniformMean_nonneg _ fun z => ih (boxDoubledFunction F z)

theorem faceIndependent_one_const {A : Type*} (b : (Fin 1 → A) → ℂ)
    (hb : FaceIndependent b 0) (a₀ : A) (u : Fin 1 → A) : b u = b (fun _ => a₀) := by
  have he : Function.update u 0 a₀ = (fun _ : Fin 1 => a₀) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  exact (he ▸ hb u a₀).symm

theorem boxCorrelation_one {A : Type*} [Fintype A] [Nonempty A]
    (F : (Fin 1 → A) → ℂ) (b : Fin 1 → (Fin 1 → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ = 1) (hi : FaceIndependent (b 0) 0) :
    ‖boxCorrelation F b‖ ^ 2 = boxMoment 0 F := by
  let a₀ : A := Classical.choice inferInstance
  simp only [boxCorrelation, Fin.prod_univ_one, faceIndependent_one_const (b 0) hi a₀,
    complexUniformMean_mul_const, norm_mul, hb, mul_one, boxMoment]

theorem box_cauchy_schwarz {A : Type*} [Fintype A] [Nonempty A] (n : ℕ) :
    ∀ (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ),
      (∀ i u, ‖b i u‖ = 1) → (∀ i, FaceIndependent (b i) i) →
      ‖boxCorrelation F b‖ ^ (2 ^ (n + 1)) ≤ boxMoment n F := by
  induction n with
  | zero =>
    intro F b hb hi
    simpa only [Nat.zero_add, pow_one] using (boxCorrelation_one F b hb (hi 0)).le
  | succ n ih =>
    intro F b hb hi
    have hstep := boxCorrelation_sq_le_doubled F b hb (hi 0)
    have hp := pow_le_pow_left₀ (sq_nonneg (‖boxCorrelation F b‖)) hstep (2 ^ (n + 1))
    have hj := realUniformMean_pow_two_le
      (fun z : A × A => ‖boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z)‖)
      (fun _ => norm_nonneg _) (n + 1)
    have hm := realUniformMean_mono
      (fun z : A × A => ‖boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z)‖ ^
        (2 ^ (n + 1)))
      (fun z : A × A => boxMoment n (boxDoubledFunction F z))
      (fun z => ih _ _ (boxDoubledFaces_norm b hb z) (boxDoubledFaces_independent b hi z))
    have hexp : 2 * 2 ^ (n + 1) = (2 : ℕ) ^ ((n + 1) + 1) := (pow_succ' 2 (n + 1)).symm
    simpa only [← pow_mul, hexp, boxMoment] using hp.trans (hj.trans hm)

theorem boxMoment_le_one {A : Type*} [Fintype A] [Nonempty A] (n : ℕ) :
    ∀ F : (Fin (n + 1) → A) → ℂ, (∀ u, ‖F u‖ ≤ 1) → boxMoment n F ≤ 1 := by
  induction n with
  | zero =>
    intro F hF
    simpa only [boxMoment, one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_complexUniformMean_le F 1 hF) 2
  | succ n ih =>
    intro F hF
    have hz (z : A × A) : boxMoment n (boxDoubledFunction F z) ≤ 1 := by
      apply ih
      intro u
      rw [boxDoubledFunction, norm_mul, Complex.norm_conj]
      have h₁ := hF (Fin.cons z.1 u)
      have h₂ := hF (Fin.cons z.2 u)
      calc
        ‖F (Fin.cons z.1 u)‖ * ‖F (Fin.cons z.2 u)‖ ≤ 1 * ‖F (Fin.cons z.2 u)‖ :=
          mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
        _ ≤ 1 := by simpa using h₂
    exact (realUniformMean_mono _ (fun _ : A × A => 1) hz).trans_eq (realUniformMean_const 1)

end GMZP0
