import GMZP0.BoxNorm

/-! The box estimate with face factors bounded by one, needed for mixed global cube arguments. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem box_remove_bounded_face {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (F : I → J → ℂ) (b : J → ℂ) (hb : ∀ y, ‖b y‖ ≤ 1) :
    ‖complexUniformMean (fun y => complexUniformMean (fun x => F x y) * b y)‖ ^ 2 ≤
      (complexUniformMean (fun z : I × I =>
        complexUniformMean (fun y => F z.1 y * conj (F z.2 y)))).re := by
  rw [← mean_inner_norm_sq_eq_pair]
  apply (norm_complexUniformMean_sq_le _).trans
  apply realUniformMean_mono
  intro y
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  calc
    _ ≤ ‖complexUniformMean (fun x => F x y)‖ * 1 :=
      mul_le_mul_of_nonneg_left (hb y) (norm_nonneg _)
    _ = _ := mul_one _

theorem boxDoubledFaces_norm_le {A : Type*} {n : ℕ}
    (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ ≤ 1) (z : A × A) (j : Fin n) (u : Fin n → A) :
    ‖boxDoubledFaces b z j u‖ ≤ 1 := by
  rw [boxDoubledFaces, norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * ‖b j.succ (Fin.cons z.2 u)‖ :=
      mul_le_mul_of_nonneg_right (hb _ _) (norm_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using hb j.succ (Fin.cons z.2 u)

theorem boxCorrelation_sq_le_doubled_bounded {A : Type*} [Fintype A] [Nonempty A] {n : ℕ}
    (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ ≤ 1) (hi : FaceIndependent (b 0) 0) :
    ‖boxCorrelation F b‖ ^ 2 ≤ realUniformMean (fun z : A × A =>
      ‖boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z)‖) := by
  let a₀ : A := Classical.choice inferInstance
  rw [boxCorrelation_split_head F b hi a₀]
  have hcs := box_remove_bounded_face (boxTailIntegrand F b) (fun u => b 0 (Fin.cons a₀ u))
    (fun u => hb 0 (Fin.cons a₀ u))
  simp only [boxTailIntegrand_pair] at hcs
  change _ ≤ (complexUniformMean (fun z : A × A =>
    boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z))).re at hcs
  rw [complexUniformMean_re] at hcs
  exact hcs.trans (realUniformMean_mono _ _ fun _ => Complex.re_le_norm _)

theorem boxCorrelation_one_bounded {A : Type*} [Fintype A] [Nonempty A]
    (F : (Fin 1 → A) → ℂ) (b : Fin 1 → (Fin 1 → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ ≤ 1) (hi : FaceIndependent (b 0) 0) :
    ‖boxCorrelation F b‖ ^ 2 ≤ boxMoment 0 F := by
  let a₀ : A := Classical.choice inferInstance
  simp only [boxCorrelation, Fin.prod_univ_one, faceIndependent_one_const (b 0) hi a₀,
    complexUniformMean_mul_const, boxMoment]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  calc
    _ ≤ ‖complexUniformMean F‖ * 1 := mul_le_mul_of_nonneg_left (hb 0 _) (norm_nonneg _)
    _ = _ := mul_one _

theorem box_cauchy_schwarz_bounded {A : Type*} [Fintype A] [Nonempty A] (n : ℕ) :
    ∀ (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ),
      (∀ i u, ‖b i u‖ ≤ 1) → (∀ i, FaceIndependent (b i) i) →
      ‖boxCorrelation F b‖ ^ (2 ^ (n + 1)) ≤ boxMoment n F := by
  induction n with
  | zero =>
    intro F b hb hi
    simpa only [Nat.zero_add, pow_one] using boxCorrelation_one_bounded F b hb (hi 0)
  | succ n ih =>
    intro F b hb hi
    have hstep := boxCorrelation_sq_le_doubled_bounded F b hb (hi 0)
    have hp := pow_le_pow_left₀ (sq_nonneg (‖boxCorrelation F b‖)) hstep (2 ^ (n + 1))
    have hj := realUniformMean_pow_two_le
      (fun z : A × A => ‖boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z)‖)
      (fun _ => norm_nonneg _) (n + 1)
    have hm := realUniformMean_mono
      (fun z : A × A => ‖boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z)‖ ^
        (2 ^ (n + 1)))
      (fun z : A × A => boxMoment n (boxDoubledFunction F z))
      (fun z => ih _ _ (boxDoubledFaces_norm_le b hb z) (boxDoubledFaces_independent b hi z))
    have hexp : 2 * 2 ^ (n + 1) = (2 : ℕ) ^ ((n + 1) + 1) := (pow_succ' 2 (n + 1)).symm
    simpa only [← pow_mul, hexp, boxMoment] using hp.trans (hj.trans hm)

theorem boxCorrelation_le_boxNorm_bounded {A : Type*} [Fintype A] [Nonempty A]
    (n : ℕ) (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ ≤ 1) (hi : ∀ i, FaceIndependent (b i) i) :
    ‖boxCorrelation F b‖ ≤ boxNorm n F := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) (boxNorm_nonneg n F)
  rw [boxNorm_pow]
  exact box_cauchy_schwarz_bounded n F b hb hi

end GMZP0
