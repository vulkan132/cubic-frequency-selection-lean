import GMZP0.FiniteFourierEnergy

/-! Exact vertical Fourier diagonalization of finite translation sums.
The coefficients may depend on the horizontal output, but not on the vertical variable. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem finiteFourier_sum {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]
    (F : I → G → ℂ) (ψ : AddChar G ℂ) :
    finiteFourier (fun y => ∑ i, F i y) ψ = ∑ i, finiteFourier (F i) ψ := by
  simp only [finiteFourier, Finset.sum_mul, complexUniformMean_sum]

theorem finiteFourier_const_mul {G : Type*} [AddCommGroup G] [Fintype G]
    (F : G → ℂ) (ψ : AddChar G ℂ) (c : ℂ) :
    finiteFourier (fun y => c * F y) ψ = c * finiteFourier F ψ := by
  simp only [finiteFourier, mul_assoc, complexUniformMean_const_mul]

/-- The positive translation y+d has multiplier psi(d) with our Fourier convention. -/
theorem finiteFourier_translate {G : Type*} [AddCommGroup G] [Fintype G]
    (F : G → ℂ) (ψ : AddChar G ℂ) (d : G) :
    finiteFourier (fun y => F (y + d)) ψ = ψ d * finiteFourier F ψ := by
  have he (y : G) : F (y + d) * conj (ψ y) =
      ψ d * (F (y + d) * conj (ψ (y + d))) := by
    symm
    rw [AddChar.map_add_eq_mul, map_mul]
    calc
      _ = (F (y + d) * conj (ψ y)) * (ψ d * conj (ψ d)) := by ring
      _ = _ := by rw [finite_character_mul_conj, mul_one]
  simp only [finiteFourier, he, complexUniformMean_const_mul]
  congr 1
  exact complexUniformMean_equiv (Equiv.addRight d) (fun y => F y * conj (ψ y))

def verticalTranslationSum {X U R G : Type*} [Fintype R] [Add G]
    (c : X → R → ℂ) (i : X → R → U) (d : R → G)
    (F : U → G → ℂ) (x : X) (y : G) : ℂ :=
  ∑ r, c x r * F (i x r) (y + d r)

def verticalFourierFiber {X U R G : Type*} [Fintype R] [AddCommGroup G]
    (c : X → R → ℂ) (i : X → R → U) (d : R → G)
    (ψ : AddChar G ℂ) (u : U → ℂ) (x : X) : ℂ :=
  ∑ r, c x r * ψ (d r) * u (i x r)

/-- Exact fiber formula, before any norm or restriction is taken. -/
theorem verticalTranslationSum_fourier {X U R G : Type*}
    [Fintype R] [AddCommGroup G] [Fintype G]
    (c : X → R → ℂ) (i : X → R → U) (d : R → G)
    (F : U → G → ℂ) (x : X) (ψ : AddChar G ℂ) :
    finiteFourier (verticalTranslationSum c i d F x) ψ =
      verticalFourierFiber c i d ψ (fun u => finiteFourier (F u) ψ) x := by
  change finiteFourier (fun y => ∑ r, c x r * F (i x r) (y + d r)) ψ = _
  simp only [finiteFourier_sum, finiteFourier_const_mul,
    finiteFourier_translate, verticalFourierFiber, mul_assoc]

/-- Uniform bounds on every Fourier fiber give the counting-energy bound, with no group-size loss. -/
theorem verticalTranslationSum_energy {X U R G : Type*}
    [Fintype X] [Fintype U] [Fintype R] [AddCommGroup G] [Fintype G]
    (c : X → R → ℂ) (i : X → R → U) (d : R → G) (B : ℝ)
    (hbound : ∀ (ψ : AddChar G ℂ) (u : U → ℂ),
      (∑ x, ‖verticalFourierFiber c i d ψ u x‖ ^ 2) ≤ B * ∑ t, ‖u t‖ ^ 2)
    (F : U → G → ℂ) :
    (∑ x, ∑ y, ‖verticalTranslationSum c i d F x y‖ ^ 2) ≤
      B * ∑ t, ∑ y, ‖F t y‖ ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ψ _ =>
    hbound ψ (fun u => finiteFourier (F u) ψ))
  have hft (ψ : AddChar G ℂ) (x : X) :
      verticalFourierFiber c i d ψ (fun u => finiteFourier (F u) ψ) x =
        finiteFourier (verticalTranslationSum c i d F x) ψ :=
    (verticalTranslationSum_fourier c i d F x ψ).symm
  simp only [hft] at h
  rw [Finset.sum_comm, ← Finset.mul_sum] at h
  have hi : (∑ ψ : AddChar G ℂ, ∑ t, ‖finiteFourier (F t) ψ‖ ^ 2) =
      ∑ t, ∑ ψ : AddChar G ℂ, ‖finiteFourier (F t) ψ‖ ^ 2 := Finset.sum_comm
  rw [hi] at h
  simp only [finiteFourier_parseval, realUniformMean, div_eq_mul_inv,
    ← Finset.sum_mul] at h
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hn : 0 < (Fintype.card G : ℝ)⁻¹ := inv_pos.mpr hcard
  rw [← mul_assoc] at h
  exact (mul_le_mul_iff_left₀ hn).mp h

end GMZP0
