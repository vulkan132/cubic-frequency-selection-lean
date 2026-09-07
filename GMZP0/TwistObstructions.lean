import GMZP0.TwistedCube

/-! Exact obstruction to extending the character-twist bound to dimension one. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem character_first_cube_obstruction {G : Type*} [AddCommGroup G] [Fintype G]
    (ψ : AddChar G ℂ) (hψ : ψ ≠ 0) :
    globalTwistedCubeMean 1 (fun y => ψ y) (Fin.cons ψ default) = 1 ∧
      globalCubeMoment 0 (fun y => ψ y) = 0 := by
  have hself : finiteFourier (fun y => ψ y) ψ = 1 := by
    simp only [finiteFourier, finite_character_mul_conj, complexUniformMean_const]
  have hzero : finiteFourier (fun y => ψ y) 0 = 0 := by
    simp only [finiteFourier, AddChar.zero_apply, map_one, mul_one, complexUniformMean]
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hψ, zero_div]
  constructor
  · rw [globalTwistedCubeMean_one, hself, norm_one, one_pow, Complex.ofReal_one]
  · rw [globalCubeMoment_one, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem dimension_one_twist_obstruction : ∃ (H : ZMod 2 → ℂ) (ψ : AddChar (ZMod 2) ℂ),
    (∀ y, ‖H y‖ = 1) ∧
      globalTwistedCubeMean 1 H (Fin.cons ψ default) = 1 ∧ globalCubeMoment 0 H = 0 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : ZMod 2))).mpr one_ne_zero
  have hn : ψ ≠ 0 := by
    intro he
    apply hψ
    simp only [he, AddChar.zero_apply]
  exact ⟨(fun y => ψ y), ψ, (fun y => ψ.norm_apply y), character_first_cube_obstruction ψ hn⟩


end GMZP0
