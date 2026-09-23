import GMZP0.OriginalBaseLogarithm
import GMZP0.RationalLatticeSandwich

/-! Apply the existing denominator theorem to the constructed actual
base logarithm. Neither a logarithmic inverse nor its origin identity
is a new input, and the original full lattice is unchanged. -/
noncomputable section
namespace GMZP0

/-- The actual constructed base logarithm satisfies both original
lattice inclusions with one positive denominator fixed before every
integer vector and every original lattice element. -/
theorem original_base_logarithmic_lattice_sandwich
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ)) (Gamma : Subgroup G)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val) :
    ∃ c : Fin m → ℚ, coord 1 = (fun j => (c j : ℝ)) ∧
      ∃ k : ℕ, 0 < k ∧
        (∀ z : Fin m → ℤ, ∃ gamma : Gamma, ∀ j,
          originalBaseLogarithm coord p c gamma j = (k : ℝ) * (z j : ℝ)) ∧
        (∀ gamma : Gamma, ∃ z : Fin m → ℤ, ∀ j,
          (k : ℝ) * originalBaseLogarithm coord p c gamma j = z j) := by
  obtain ⟨z, hz⟩ := hint ⟨1, Gamma.one_mem⟩
  let c : Fin m → ℚ := fun i => (z i : ℚ)
  have hc : coord 1 = fun j => (c j : ℝ) := by simpa only [c, Rat.cast_intCast] using hz
  obtain ⟨E, L, e, he, hlog, hE, hL, he0, ht⟩ :=
    original_rational_base_time_one_equiv coord p hjoint q htri hlow c hc
  have hzero : e.symm 1 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply, he0]
  obtain ⟨k, hk, hlo, hhi⟩ := original_logarithmic_lattice_sandwich Gamma coord e.symm
    hint hcover E L hE hL hzero
  refine ⟨c, hc, k, hk, ?_, ?_⟩
  · intro z
    obtain ⟨gamma, hg⟩ := hlo z
    exact ⟨gamma, fun j => by simpa only [hlog] using hg j⟩
  · intro gamma
    obtain ⟨z, hz⟩ := hhi gamma
    exact ⟨z, fun j => by simpa only [hlog] using hz j⟩

end GMZP0
