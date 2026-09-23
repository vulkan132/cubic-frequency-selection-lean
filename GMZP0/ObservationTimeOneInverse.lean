import GMZP0.OriginalBaseLogarithm
import GMZP0.OriginalFullOneParameter
import GMZP0.OriginalSubgroupTangent

/-! The actual original H time-one map is globally invertible. Its
inverse retains the original base logarithm and applies the same
proved rational fiber inverse at that logarithmic tangent. -/
noncomputable section
open Module
namespace GMZP0

/-- Combine a genuine original base equivalence with two-sided fiber
operators, on the entire original observation space. -/
def observationFiberEquiv {G X : Type*} [Group G]
    (V : ObservationModule G) (e : X ≃ G)
    (F J : X → Module.End ℝ V.space)
    (hJF : ∀ x, J x * F x = 1) (hFJ : ∀ x, F x * J x = 1) :
    (X × V.space) ≃ ObservationGroup V where
  toFun a := ⟨e a.1, F a.1 a.2⟩
  invFun a := (e.symm a.base, J (e.symm a.base) a.obs)
  left_inv := by
    rintro ⟨x, Q⟩
    apply Prod.ext
    · exact e.symm_apply_apply x
    · change J (e.symm (e x)) (F x Q) = Q
      rw [e.symm_apply_apply]
      change (J x * F x) Q = Q
      rw [hJF]
      rfl
  right_inv := by
    intro a
    apply ObservationGroup.ext
    · exact e.apply_symm_apply a.base
    · change F (e.symm a.base) (J (e.symm a.base) a.obs) = a.obs
      change (F (e.symm a.base) * J (e.symm a.base)) a.obs = a.obs
      rw [hFJ]
      rfl

/-- The original structural presentation constructs a globally
invertible actual H time-one map in the same full integer/real bases.
The inverse formula uses the newly constructed original base logarithm,
with no new base inverse or fiber inverse premise. -/
theorem original_integral_basis_time_one_equiv_with_subgroups
    {G iota : Type*} [Group G] [TopologicalSpace G] [Fintype iota] {m : ℕ}
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    ∃ c : Fin m → ℚ, ∃ d : ℕ,
      ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space, ∃ B : Fin d → MvPolynomial (Fin m) ℚ,
      ∃ K : ℕ, ∃ A : Fin d → Fin d → Fin m → ℚ, ∃ E L : Polynomial ℚ,
        coord 1 = (fun i => (c i : ℝ)) ∧ (∀ i, bR i = (bZ i).val) ∧
        (∀ i g, bR i g = MvPolynomial.aeval (coord g) (B i)) ∧ 0 < K ∧
        (∀ v : Fin m → ℝ, (observationCoordinateDifferential V bR A v) ^ K = 0) ∧
        (∀ v : Fin m → ℝ,
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E =
            nilpotentFiberMatrix K (observationCoordinateDifferential V bR A v) ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) L *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) E = 1 ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) L = 1) ∧
        ∃ e : ((Fin m → ℝ) × V.space) ≃ ObservationGroup V,
          (∀ v Q, e (v, Q) = observationOneParameterLift V
            (originalBaseOneParameter coord.toEquiv p c v) K
            (observationCoordinateDifferential V bR A v) Q 1) ∧
          (∀ a : ObservationGroup V, e.symm a =
            (originalBaseLogarithm coord.toEquiv p c a.base,
              Polynomial.aeval (observationCoordinateDifferential V bR A
                (originalBaseLogarithm coord.toEquiv p c a.base)) L a.obs)) ∧
          e (0, 0) = 1 ∧
          (∀ v Q, OriginalCoordinateSubgroup (observationFullCoordinates V coord bR)
            (observationOneParameterLift V (originalBaseOneParameter coord.toEquiv p c v)
              K (observationCoordinateDifferential V bR A v) Q)
            (Sum.elim v (bR.equivFun Q))) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  obtain ⟨c, d, bZ, bR, B, K, A, E, L, hc, hcompat, hB, hK, hpow, hpoly, hpaths⟩ :=
    original_integral_basis_full_one_parameter V Gamma coord b hint hcover p hjoint q htri hlow P hP
  obtain ⟨EG, LG, eG, heG, hlogG, hEG, hLG, heG0, htG⟩ :=
    original_rational_base_time_one_equiv coord.toEquiv p hjoint q htri hlow c hc
  let e := observationFiberEquiv V eG
    (fun v => Polynomial.aeval (observationCoordinateDifferential V bR A v) E)
    (fun v => Polynomial.aeval (observationCoordinateDifferential V bR A v) L)
    (fun v => (hpoly v).2.1) (fun v => (hpoly v).2.2)
  refine ⟨c, d, bZ, bR, B, K, A, E, L, hc, hcompat, hB, hK, hpow, hpoly, e, ?_, ?_, ?_, ?_⟩
  · intro v Q
    obtain ⟨hb0, hadd, hv, hcoord, hT, hLift⟩ := hpaths v
    obtain ⟨h0, hm, hd, h1, hu⟩ := hLift Q
    change (⟨eG v, Polynomial.aeval (observationCoordinateDifferential V bR A v) E Q⟩ : ObservationGroup V) = _
    rw [heG]
    exact h1.symm
  · intro a
    change (eG.symm a.base,
      Polynomial.aeval (observationCoordinateDifferential V bR A (eG.symm a.base)) L a.obs) = _
    rw [hlogG]
  · change (⟨eG 0, Polynomial.aeval (observationCoordinateDifferential V bR A 0) E 0⟩ : ObservationGroup V) = 1
    apply ObservationGroup.ext
    · exact heG0
    · exact map_zero _

  · intro v Q
    obtain ⟨hb0, hadd, hv, hcoord, hT, hLift⟩ := hpaths v
    obtain ⟨h0, hm, hd, h1, hu⟩ := hLift Q
    exact ⟨h0, hm, hd, fun eta heta hdeta => funext (hu eta heta hdeta)⟩

/-- Backwards-compatible projection of the stronger same-witness theorem. -/
theorem original_integral_basis_time_one_equiv
    {G iota : Type*} [Group G] [TopologicalSpace G] [Fintype iota] {m : ℕ}
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    ∃ c : Fin m → ℚ, ∃ d : ℕ,
      ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space, ∃ B : Fin d → MvPolynomial (Fin m) ℚ,
      ∃ K : ℕ, ∃ A : Fin d → Fin d → Fin m → ℚ, ∃ E L : Polynomial ℚ,
        coord 1 = (fun i => (c i : ℝ)) ∧ (∀ i, bR i = (bZ i).val) ∧
        (∀ i g, bR i g = MvPolynomial.aeval (coord g) (B i)) ∧ 0 < K ∧
        (∀ v : Fin m → ℝ, (observationCoordinateDifferential V bR A v) ^ K = 0) ∧
        (∀ v : Fin m → ℝ,
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E =
            nilpotentFiberMatrix K (observationCoordinateDifferential V bR A v) ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) L *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) E = 1 ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) L = 1) ∧
        ∃ e : ((Fin m → ℝ) × V.space) ≃ ObservationGroup V,
          (∀ v Q, e (v, Q) = observationOneParameterLift V
            (originalBaseOneParameter coord.toEquiv p c v) K
            (observationCoordinateDifferential V bR A v) Q 1) ∧
          (∀ a : ObservationGroup V, e.symm a =
            (originalBaseLogarithm coord.toEquiv p c a.base,
              Polynomial.aeval (observationCoordinateDifferential V bR A
                (originalBaseLogarithm coord.toEquiv p c a.base)) L a.obs)) ∧
          e (0, 0) = 1 := by
  obtain ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly,
      e, he, hi, he0, _⟩ :=
    original_integral_basis_time_one_equiv_with_subgroups V Gamma coord b hint hcover
      p hjoint q htri hlow P hP
  exact ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly, e, he, hi, he0⟩

end GMZP0
