import GMZP0.MeanAlgebra

/-! One exact coordinate-doubling Cauchy–Schwarz step for finite box averages. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem complexUniformMean_pair_mul_conj {I J : Type*} [Fintype I] [Fintype J]
    (F : I → ℂ) (G : J → ℂ) :
    complexUniformMean (fun z : I × J => F z.1 * conj (G z.2)) =
      complexUniformMean F * conj (complexUniformMean G) := by
  rw [complexUniformMean_prod (fun i j => F i * conj (G j))]
  simp only [complexUniformMean_const_mul, complexUniformMean_conj, complexUniformMean_mul_const]

theorem complexUniformMean_pair_norm_sq {I : Type*} [Fintype I] (F : I → ℂ) :
    (complexUniformMean (fun z : I × I => F z.1 * conj (F z.2))).re =
      ‖complexUniformMean F‖ ^ 2 := by
  rw [complexUniformMean_pair_mul_conj, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem mean_inner_norm_sq_eq_pair {I J : Type*} [Fintype I] [Fintype J] (F : I → J → ℂ) :
    realUniformMean (fun y => ‖complexUniformMean (fun x => F x y)‖ ^ 2) =
      (complexUniformMean (fun z : I × I =>
        complexUniformMean (fun y => F z.1 y * conj (F z.2 y)))).re := by
  simp_rw [← complexUniformMean_pair_norm_sq]
  rw [← complexUniformMean_re, complexUniformMean_comm]

theorem box_remove_unit_face {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (F : I → J → ℂ) (b : J → ℂ) (hb : ∀ y, ‖b y‖ = 1) :
    ‖complexUniformMean (fun y => complexUniformMean (fun x => F x y) * b y)‖ ^ 2 ≤
      (complexUniformMean (fun z : I × I =>
        complexUniformMean (fun y => F z.1 y * conj (F z.2 y)))).re := by
  rw [← mean_inner_norm_sq_eq_pair]
  simpa only [norm_mul, hb, mul_one] using
    norm_complexUniformMean_sq_le (fun y => complexUniformMean (fun x => F x y) * b y)

theorem box_remove_unit_face_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (F : I → J → ℂ) :
    0 ≤ (complexUniformMean (fun z : I × I =>
      complexUniformMean (fun y => F z.1 y * conj (F z.2 y)))).re := by
  rw [← mean_inner_norm_sq_eq_pair]
  exact realUniformMean_nonneg _ fun _ => sq_nonneg _

end GMZP0
