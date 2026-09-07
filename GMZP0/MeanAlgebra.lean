import GMZP0.FiniteAverages

/-! Finite probability means: exact reindexing, conjugation, and moment inequalities. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem realUniformMean_nonneg {I : Type*} [Fintype I] (F : I → ℝ)
    (hF : ∀ i, 0 ≤ F i) : 0 ≤ realUniformMean F :=
  div_nonneg (Finset.sum_nonneg fun i _ => hF i) (Nat.cast_nonneg _)

theorem realUniformMean_mono {I : Type*} [Fintype I] (F G : I → ℝ)
    (hFG : ∀ i, F i ≤ G i) : realUniformMean F ≤ realUniformMean G :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hFG i) (Nat.cast_nonneg _)

theorem realUniformMean_const {I : Type*} [Fintype I] [Nonempty I] (c : ℝ) :
    realUniformMean (fun _ : I => c) = c := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [realUniformMean, hn]

theorem realUniformMean_const_mul {I : Type*} [Fintype I] (F : I → ℝ) (c : ℝ) :
    realUniformMean (fun i => c * F i) = c * realUniformMean F := by
  simp only [realUniformMean, ← Finset.mul_sum]
  ring

theorem complexUniformMean_mul_const {I : Type*} [Fintype I] (F : I → ℂ) (c : ℂ) :
    complexUniformMean (fun i => F i * c) = complexUniformMean F * c := by
  simp only [complexUniformMean, ← Finset.sum_mul]
  ring

theorem complexUniformMean_const_mul {I : Type*} [Fintype I] (F : I → ℂ) (c : ℂ) :
    complexUniformMean (fun i => c * F i) = c * complexUniformMean F := by
  simp only [complexUniformMean, ← Finset.mul_sum]
  ring

theorem complexUniformMean_conj {I : Type*} [Fintype I] (F : I → ℂ) :
    complexUniformMean (fun i => conj (F i)) = conj (complexUniformMean F) := by
  simp only [complexUniformMean, map_div₀, map_sum, map_natCast]

theorem complexUniformMean_re {I : Type*} [Fintype I] (F : I → ℂ) :
    (complexUniformMean F).re = realUniformMean (fun i => (F i).re) := by
  unfold complexUniformMean realUniformMean
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum]

theorem complexUniformMean_prod {I J : Type*} [Fintype I] [Fintype J] (F : I → J → ℂ) :
    complexUniformMean (fun z : I × J => F z.1 z.2) =
      complexUniformMean (fun i => complexUniformMean (F i)) := by
  simp only [complexUniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem realUniformMean_prod {I J : Type*} [Fintype I] [Fintype J] (F : I → J → ℝ) :
    realUniformMean (fun z : I × J => F z.1 z.2) =
      realUniformMean (fun i => realUniformMean (F i)) := by
  simp only [realUniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem complexUniformMean_comm {I J : Type*} [Fintype I] [Fintype J] (F : I → J → ℂ) :
    complexUniformMean (fun i => complexUniformMean (F i)) =
      complexUniformMean (fun j => complexUniformMean (fun i => F i j)) := by
  simp only [complexUniformMean, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem complexUniformMean_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (F : J → ℂ) : complexUniformMean (fun i => F (e i)) = complexUniformMean F := by
  unfold complexUniformMean
  rw [Equiv.sum_comp e F, Fintype.card_congr e]

theorem complexUniformMean_cons {A : Type*} [Fintype A] (n : ℕ)
    (F : (Fin (n + 1) → A) → ℂ) :
    complexUniformMean F = complexUniformMean (fun a : A =>
      complexUniformMean (fun u : Fin n → A => F (Fin.cons a u))) := by
  rw [← complexUniformMean_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => A)) F]
  exact complexUniformMean_prod (fun (a : A) (u : Fin n → A) => F (Fin.cons a u))

theorem norm_complexUniformMean_le_mean_norm {I : Type*} [Fintype I] (F : I → ℂ) :
    ‖complexUniformMean F‖ ≤ realUniformMean (fun i => ‖F i‖) := by
  rw [complexUniformMean, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg _)

theorem realUniformMean_sq_le {I : Type*} [Fintype I] [Nonempty I] (F : I → ℝ) :
    realUniformMean F ^ 2 ≤ realUniformMean (fun i => F i ^ 2) := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hcs : (∑ i, F i) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, F i ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1 : ℝ)) F
  unfold realUniformMean
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hn)]
  calc
    (∑ i, F i) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, F i ^ 2 := hcs
    _ = ((∑ i, F i ^ 2) / (Fintype.card I : ℝ)) * (Fintype.card I : ℝ) ^ 2 := by
      field_simp

theorem norm_complexUniformMean_sq_le {I : Type*} [Fintype I] [Nonempty I] (F : I → ℂ) :
    ‖complexUniformMean F‖ ^ 2 ≤ realUniformMean (fun i => ‖F i‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_complexUniformMean_le_mean_norm F) 2).trans
    (realUniformMean_sq_le _)

theorem realUniformMean_pow_two_le {I : Type*} [Fintype I] [Nonempty I]
    (F : I → ℝ) (hF : ∀ i, 0 ≤ F i) (n : ℕ) :
    realUniformMean F ^ (2 ^ n) ≤ realUniformMean (fun i => F i ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow := pow_le_pow_left₀ (pow_nonneg (realUniformMean_nonneg F hF) _) ih 2
    have hcs := realUniformMean_sq_le (fun i => F i ^ (2 ^ n))
    simpa only [← pow_mul, show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n]
      using hpow.trans hcs

end GMZP0
