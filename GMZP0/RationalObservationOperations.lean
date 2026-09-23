import GMZP0.RationalObservationInverse

/-! One original coordinate presentation simultaneously has rational
multiplication, rational inverse and the exact full integer lattice. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {G iota : Type*} [Group G] [TopologicalSpace G] [Fintype iota] {m : ℕ}

/-- Original rational and strict triangular base laws construct rational
formulas for both actual H operations in one compatible basis, together
with the entire original integer lattice in those very same coordinates. -/
theorem observation_rational_operations_full_lattice
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u s, coord (g * u) s = coord u s + MvPolynomial.aeval (coord u) (q g s))
    (hlow : ∀ g s d, d ∈ (q g s).support → ∀ j ∈ d.support, j.val < s.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ d : ℕ, ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space,
      ∃ M : (Fin m ⊕ Fin d) → MvPolynomial ((Fin m ⊕ Fin d) ⊕ (Fin m ⊕ Fin d)) ℚ,
      ∃ R : (Fin m ⊕ Fin d) → MvPolynomial (Fin m ⊕ Fin d) ℚ,
        (∀ i, bR i = (bZ i).val) ∧
        (∀ a e : ObservationGroup V, ∀ s,
          observationFullCoordinates V coord bR (a * e) s =
            MvPolynomial.aeval (Sum.elim (observationFullCoordinates V coord bR a)
              (observationFullCoordinates V coord bR e)) (M s)) ∧
        (∀ a : ObservationGroup V, ∀ s,
          observationFullCoordinates V coord bR a⁻¹ s =
            MvPolynomial.aeval (observationFullCoordinates V coord bR a) (R s)) ∧
        (∀ a : ObservationGroup V, a ∈ observationLatticeSubgroup V Gamma ↔
          ∃ z : (Fin m ⊕ Fin d) → ℤ, observationFullCoordinates V coord bR a = fun s => (z s : ℝ)) := by
  obtain ⟨d, bZ, bR, B, hb, hB⟩ := observation_compatible_rational_bases V Gamma b coord hint hcover P hP
  obtain ⟨M, hM⟩ := observation_group_rational_polynomial_presentation V Gamma coord bR hint hcover p hjoint B hB
  obtain ⟨R, hR⟩ := observation_group_rational_inverse_presentation V Gamma coord bR hint hcover p hjoint q htri hlow B hB
  exact ⟨d, bZ, bR, M, R, hb, hM, hR,
    observation_lattice_full_integer_coordinates V Gamma coord hint hcover bZ bR hb⟩

end GMZP0
