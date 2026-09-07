import GMZP0.CubeExpansion

/-! Pushforward density relative to uniform group measure, with all parameter multiplicities. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def parameterDensity {G A : Type*} [Fintype G] [Fintype A] [DecidableEq G]
    (r : A → G) (x : G) : ℝ :=
  realUniformMean (fun a : A => if r a = x then (Fintype.card G : ℝ) else 0)

theorem parameterDensity_nonneg {G A : Type*} [Fintype G] [Fintype A] [DecidableEq G]
    (r : A → G) (x : G) : 0 ≤ parameterDensity r x := by
  apply realUniformMean_nonneg
  intro a
  split_ifs <;> positivity

theorem parameterDensity_card {G A : Type*} [Fintype G] [Fintype A] [DecidableEq G]
    (r : A → G) (x : G) :
    parameterDensity r x = (Fintype.card G : ℝ) * (Finset.univ.filter (fun a => r a = x)).card / Fintype.card A := by
  classical
  simp only [parameterDensity, realUniformMean, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

theorem parameterDensity_pushforward {G A : Type*} [Fintype G] [Nonempty G] [Fintype A] [DecidableEq G]
    (r : A → G) (F : G → ℂ) :
    complexUniformMean (fun x => (parameterDensity r x : ℂ) * F x) = complexUniformMean (fun a => F (r a)) := by
  have hd (x : G) : (parameterDensity r x : ℂ) =
      complexUniformMean (fun a => if r a = x then (Fintype.card G : ℂ) else 0) := by
    rw [parameterDensity, ← complexUniformMean_ofReal]
    congr 1
    funext a
    split_ifs <;> simp
  simp only [hd, ← complexUniformMean_mul_const]
  rw [complexUniformMean_comm]
  congr 1
  funext a
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [complexUniformMean, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact mul_div_cancel_left₀ _ hn

theorem parameterDensity_mean_one {G A : Type*} [Fintype G] [Nonempty G] [Fintype A] [Nonempty A] [DecidableEq G]
    (r : A → G) : realUniformMean (parameterDensity r) = 1 := by
  have h := parameterDensity_pushforward r (fun _ => (1 : ℂ))
  simp only [mul_one, complexUniformMean_ofReal, complexUniformMean_const] at h
  exact_mod_cast h

end GMZP0
