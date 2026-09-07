import GMZP0.BoxCauchyStep

/-! Face families and their exact transformation when a coordinate is doubled. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def FaceIndependent {A : Type*} {d : ℕ} (b : (Fin d → A) → ℂ) (i : Fin d) : Prop :=
  ∀ u a, b (Function.update u i a) = b u

def boxCorrelation {A : Type*} [Fintype A] {d : ℕ}
    (F : (Fin d → A) → ℂ) (b : Fin d → (Fin d → A) → ℂ) : ℂ :=
  complexUniformMean (fun u => F u * ∏ i, b i u)

def boxTailIntegrand {A : Type*} {n : ℕ} (F : (Fin (n + 1) → A) → ℂ)
    (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ) (a : A) (u : Fin n → A) : ℂ :=
  F (Fin.cons a u) * ∏ j : Fin n, b j.succ (Fin.cons a u)

def boxDoubledFunction {A : Type*} {n : ℕ} (F : (Fin (n + 1) → A) → ℂ)
    (z : A × A) (u : Fin n → A) : ℂ := F (Fin.cons z.1 u) * conj (F (Fin.cons z.2 u))

def boxDoubledFaces {A : Type*} {n : ℕ}
    (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ) (z : A × A)
    (j : Fin n) (u : Fin n → A) : ℂ :=
  b j.succ (Fin.cons z.1 u) * conj (b j.succ (Fin.cons z.2 u))

theorem boxDoubledFaces_norm {A : Type*} {n : ℕ}
    (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ = 1) (z : A × A) (j : Fin n) (u : Fin n → A) :
    ‖boxDoubledFaces b z j u‖ = 1 := by
  simp only [boxDoubledFaces, norm_mul, Complex.norm_conj, hb, mul_one]

theorem boxDoubledFaces_independent {A : Type*} {n : ℕ}
    (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i, FaceIndependent (b i) i) (z : A × A) (j : Fin n) :
    FaceIndependent (boxDoubledFaces b z j) j := by
  have hj := hb j.succ
  unfold FaceIndependent at hj
  intro u a
  simp only [boxDoubledFaces, Fin.cons_update, hj]

theorem boxTailIntegrand_pair {A : Type*} {n : ℕ}
    (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (z : A × A) (u : Fin n → A) :
    boxTailIntegrand F b z.1 u * conj (boxTailIntegrand F b z.2 u) =
      boxDoubledFunction F z u * ∏ j, boxDoubledFaces b z j u := by
  simp only [boxTailIntegrand, boxDoubledFunction, boxDoubledFaces, map_mul, map_prod,
    Finset.prod_mul_distrib]
  ring

theorem boxCorrelation_split_head {A : Type*} [Fintype A] {n : ℕ}
    (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : FaceIndependent (b 0) 0) (a₀ : A) :
    boxCorrelation F b = complexUniformMean (fun u : Fin n → A =>
      complexUniformMean (fun a : A => boxTailIntegrand F b a u) * b 0 (Fin.cons a₀ u)) := by
  have hhead (u : Fin n → A) (a : A) : b 0 (Fin.cons a u) = b 0 (Fin.cons a₀ u) := by
    have hh : b 0 (Fin.cons a₀ u) = b 0 (Fin.cons a u) := by
      simpa only [Fin.update_cons_zero] using hb (Fin.cons a u) a₀
    exact hh.symm
  unfold boxCorrelation
  rw [complexUniformMean_cons, complexUniformMean_comm]
  congr 1
  funext u
  rw [← complexUniformMean_mul_const]
  congr 1
  funext a
  rw [Fin.prod_univ_succ, hhead]
  unfold boxTailIntegrand
  ring

theorem boxCorrelation_sq_le_doubled {A : Type*} [Fintype A] [Nonempty A] {n : ℕ}
    (F : (Fin (n + 1) → A) → ℂ) (b : Fin (n + 1) → (Fin (n + 1) → A) → ℂ)
    (hb : ∀ i u, ‖b i u‖ = 1) (hi : FaceIndependent (b 0) 0) :
    ‖boxCorrelation F b‖ ^ 2 ≤ realUniformMean (fun z : A × A =>
      ‖boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z)‖) := by
  let a₀ : A := Classical.choice inferInstance
  rw [boxCorrelation_split_head F b hi a₀]
  have hcs := box_remove_unit_face (boxTailIntegrand F b) (fun u => b 0 (Fin.cons a₀ u))
    (fun u => hb 0 (Fin.cons a₀ u))
  simp only [boxTailIntegrand_pair] at hcs
  change _ ≤ (complexUniformMean (fun z : A × A =>
    boxCorrelation (boxDoubledFunction F z) (boxDoubledFaces b z))).re at hcs
  rw [complexUniformMean_re] at hcs
  exact hcs.trans (realUniformMean_mono _ _ fun _ => Complex.re_le_norm _)

end GMZP0
