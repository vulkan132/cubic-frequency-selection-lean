import GMZP0.LocalCubeNorm
import GMZP0.ParameterDensity

/-! Uniform-density normalization and a constant-function obstruction to using probability masses. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem parameterDensity_identity {G : Type*} [Fintype G] [Nonempty G] [DecidableEq G] (x : G) :
    parameterDensity (fun y : G => y) x = 1 := by
  have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [parameterDensity, realUniformMean, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    div_self hn]

theorem localCubeMoment_const_one {G A : Type*} [AddCommGroup G] [Fintype G]
    [Fintype A] [Nonempty A] (n : ℕ) (r : A → G) : localCubeMoment n (fun _ : G => (1 : ℂ)) r = 1 := by
  have h := localCubeMoment_complex n (fun _ : G => (1 : ℂ)) r
  have hconj (ω : Fin (n + 1) → Bool) : cubeConj (n + 1) ω 1 = 1 := by
    simpa only [Complex.ofReal_one] using cubeConj_ofReal (n + 1) ω 1
  simp only [cubeMean, cubeProduct, localBoxFunction, hconj, Finset.prod_const_one,
    complexUniformMean_const] at h
  exact_mod_cast h.symm

theorem raw_probability_density_obstruction :
    (∑ _ : ZMod 2, (1 / 2 : ℝ)) = 1 ∧
    realUniformMean (fun _ : ZMod 2 => (1 / 2 : ℝ)) = 1 / 2 ∧
    localCubeMoment 3 (fun _ : ZMod 2 => (1 : ℂ)) (fun y : ZMod 2 => y) >
      realUniformMean (fun _ : ZMod 2 => (1 / 2 : ℝ) ^ 2) ^ 4 *
        localCubeMoment 3 (fun _ : ZMod 2 => (1 : ℂ)) (fun y : ZMod 2 => y) := by
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    realUniformMean_const, localCubeMoment_const_one]
  norm_num

end GMZP0
