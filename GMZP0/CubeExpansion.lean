import GMZP0.CubeConjugation

/-! Complete Boolean-vertex expansion of the recursive box moment, with multiplicities. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem complexUniformMean_unique {I : Type*} [Fintype I] [Unique I] (F : I → ℂ) :
    complexUniformMean F = F default := by
  simp [complexUniformMean]

theorem complexUniformMean_ofReal {I : Type*} [Fintype I] (F : I → ℝ) :
    complexUniformMean (fun i => (F i : ℂ)) = (realUniformMean F : ℂ) := by
  simp only [complexUniformMean, realUniformMean, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast]

def cubeVertex {A : Type*} {d : ℕ} (v : Fin d → A × A) (ω : Fin d → Bool) : Fin d → A :=
  fun i => if ω i then (v i).2 else (v i).1

def cubeProduct {A : Type*} (d : ℕ) (F : (Fin d → A) → ℂ) (v : Fin d → A × A) : ℂ :=
  ∏ ω : Fin d → Bool, cubeConj d ω (F (cubeVertex v ω))

def cubeMean {A : Type*} [Fintype A] (d : ℕ) (F : (Fin d → A) → ℂ) : ℂ :=
  complexUniformMean (fun v : Fin d → A × A => cubeProduct d F v)

theorem prod_boolean_cons (d : ℕ) (F : (Fin (d + 1) → Bool) → ℂ) :
    (∏ ω, F ω) = (∏ ω : Fin d → Bool, F (Fin.cons false ω)) *
      ∏ ω : Fin d → Bool, F (Fin.cons true ω) := by
  rw [← Equiv.prod_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)) F]
  change (∏ z : Bool × (Fin d → Bool), F (Fin.cons z.1 z.2)) = _
  simp only [Fintype.prod_prod_type, Fintype.prod_bool]
  ring

theorem cubeVertex_cons {A : Type*} {d : ℕ} (z : A × A) (v : Fin d → A × A)
    (b : Bool) (ω : Fin d → Bool) :
    cubeVertex (Fin.cons z v) (Fin.cons b ω) =
      Fin.cons (if b then z.2 else z.1) (cubeVertex v ω) := by
  funext i
  cases i using Fin.cases <;> simp [cubeVertex]

theorem cubeProduct_zero {A : Type*} (F : (Fin 0 → A) → ℂ) (v : Fin 0 → A × A) :
    cubeProduct 0 F v = F default := by
  simp only [cubeProduct, cubeConj, Fintype.prod_unique]
  congr 1
  exact Subsingleton.elim _ _

theorem cubeProduct_succ {A : Type*} (d : ℕ) (F : (Fin (d + 1) → A) → ℂ)
    (z : A × A) (v : Fin d → A × A) :
    cubeProduct (d + 1) F (Fin.cons z v) = cubeProduct d (boxDoubledFunction F z) v := by
  rw [cubeProduct, prod_boolean_cons]
  simp only [cubeVertex_cons, cubeConj, Fin.cons_zero, Fin.tail_cons, Bool.false_eq_true,
    if_false, if_true, cubeProduct, boxDoubledFunction, cubeConj_mul, cubeConj_conj,
    Finset.prod_mul_distrib]

theorem cubeMean_succ {A : Type*} [Fintype A] (d : ℕ) (F : (Fin (d + 1) → A) → ℂ) :
    cubeMean (d + 1) F = complexUniformMean (fun z : A × A => cubeMean d (boxDoubledFunction F z)) := by
  unfold cubeMean
  rw [complexUniformMean_cons]
  simp only [cubeProduct_succ]

theorem cubeMean_one {A : Type*} [Fintype A] (F : (Fin 1 → A) → ℂ) :
    cubeMean 1 F = (‖complexUniformMean F‖ ^ 2 : ℝ) := by
  have hF : complexUniformMean F = complexUniformMean (fun a : A => F (Fin.cons a default)) := by
    rw [complexUniformMean_cons 0]
    simp only [complexUniformMean_unique]
  rw [cubeMean_succ]
  simp only [cubeMean, cubeProduct_zero, complexUniformMean_unique, boxDoubledFunction]
  rw [complexUniformMean_pair_mul_conj (fun a : A => F (Fin.cons a default))
    (fun a : A => F (Fin.cons a default)), ← hF, Complex.mul_conj, ← Complex.sq_norm]

/-- Equality in C, not merely equality of real parts. All repeated vertices are included. -/
theorem cubeMean_eq_boxMoment {A : Type*} [Fintype A] (n : ℕ) :
    ∀ F : (Fin (n + 1) → A) → ℂ, cubeMean (n + 1) F = (boxMoment n F : ℂ) := by
  induction n with
  | zero => intro F; exact cubeMean_one F
  | succ n ih =>
    intro F
    rw [cubeMean_succ]
    simp only [ih, complexUniformMean_ofReal, boxMoment]

theorem boxMoment_eq_cubeMean_re {A : Type*} [Fintype A] (n : ℕ)
    (F : (Fin (n + 1) → A) → ℂ) : boxMoment n F = (cubeMean (n + 1) F).re := by
  rw [cubeMean_eq_boxMoment, Complex.ofReal_re]

theorem cubeMean_nonneg_real {A : Type*} [Fintype A] (n : ℕ)
    (F : (Fin (n + 1) → A) → ℂ) : 0 ≤ (cubeMean (n + 1) F).re ∧ (cubeMean (n + 1) F).im = 0 := by
  simp only [cubeMean_eq_boxMoment, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨boxMoment_nonneg n F, trivial⟩

end GMZP0
