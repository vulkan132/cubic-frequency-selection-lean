import GMZP0.CubeExpansion

/-! Tensorization of an exact finite pushforward law, retaining every sampled coordinate. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_product_pushforward {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B) (w : B → ℂ)
    (hpush : ∀ T : B → ℂ, complexUniformMean (fun b => w b * T b) =
      complexUniformMean (fun a => T (r a))) (d : ℕ) :
    ∀ T : (Fin d → B) → ℂ,
      complexUniformMean (fun v => (∏ i, w (v i)) * T v) =
        complexUniformMean (fun u : Fin d → A => T (fun i => r (u i))) := by
  induction d with
  | zero =>
    intro T
    simp only [Fin.prod_univ_zero, one_mul, complexUniformMean_unique]
    congr 1
    exact Subsingleton.elim _ _
  | succ d ih =>
    intro T
    calc
      _ = complexUniformMean (fun b : B => w b * complexUniformMean
          (fun v : Fin d → B => (∏ i, w (v i)) * T (Fin.cons b v))) := by
        rw [complexUniformMean_cons]
        congr 1
        funext b
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [← complexUniformMean_const_mul]
        congr 1
        funext v
        ring
      _ = complexUniformMean (fun b : B => w b * complexUniformMean
          (fun u : Fin d → A => T (Fin.cons b (fun i => r (u i))))) := by
        congr 1
        funext b
        rw [ih]
      _ = complexUniformMean (fun a : A => complexUniformMean
          (fun u : Fin d → A => T (Fin.cons (r a) (fun i => r (u i))))) := hpush _
      _ = _ := by
        rw [complexUniformMean_cons]
        congr 1
        funext a
        congr 1
        funext u
        congr 1
        funext i
        cases i using Fin.cases <;> simp

end GMZP0
