import GMZP0.ObservationIntegerRationalBasis
import GMZP0.RationalObservationGroup

/-! Identify the actual observation lattice with the entire integer grid
in the same coordinates used by the derived rational multiplication law. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype iota]

/-- Compatible actual bases read the same integer coordinates before and
after embedding the original integer lattice into the real function space. -/
theorem observation_compatible_basis_integer_coordinates
    (V : ObservationModule G) (Gamma : Subgroup G)
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) (F : observationIntegerLattice V Gamma) (i : iota) :
    bR.equivFun F.val i = (bZ.equivFun F i : ℝ) := by
  classical
  have he := congrArg (observationIntegerLattice V Gamma).subtype (bZ.sum_equivFun F)
  simp only [map_sum, map_smul, Submodule.subtype_apply] at he
  rw [← he]
  have hh (j : iota) : (bZ j).val = bR j := (hb j).symm
  simp [hh, Finsupp.single_apply]

variable [TopologicalSpace G]

/-- The entire actual H lattice, not a chosen sublattice, is exactly the
integer grid of the original base and compatible integer-fiber coordinates. -/
theorem observation_lattice_full_integer_coordinates
    (V : ObservationModule G) (Gamma : Subgroup G) (coord : G ≃ₜ (sigma → ℝ))
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val) (a : ObservationGroup V) :
    a ∈ observationLatticeSubgroup V Gamma ↔
      ∃ z : (sigma ⊕ iota) → ℤ, observationFullCoordinates V coord bR a = fun s => (z s : ℝ) := by
  classical
  constructor
  · intro ha
    obtain ⟨zG, hzG⟩ := hint ⟨a.base, ha.1⟩
    let F : observationIntegerLattice V Gamma := ⟨a.obs, ha.2⟩
    refine ⟨Sum.elim zG (bZ.equivFun F), ?_⟩
    funext s
    cases s with
    | inl s => exact congrFun hzG s
    | inr i => exact observation_compatible_basis_integer_coordinates V Gamma bZ bR hb F i
  · rintro ⟨z, hz⟩
    obtain ⟨gamma, hgamma⟩ := hcover (fun s => z (Sum.inl s))
    have hg : a.base = gamma := coord.injective (by
      funext s
      exact (congrFun hz (Sum.inl s)).trans (congrFun hgamma s).symm)
    let F : observationIntegerLattice V Gamma := bZ.equivFun.symm (fun i => z (Sum.inr i))
    have hf : a.obs = F.val := bR.equivFun.injective (by
      funext i
      rw [observation_compatible_basis_integer_coordinates V Gamma bZ bR hb F i]
      simpa only [F, LinearEquiv.apply_symm_apply, observation_full_coordinates_fiber]
        using congrFun hz (Sum.inr i))
    exact ⟨hg ▸ gamma.property, hf ▸ F.property⟩

/-- Original rational base and function data construct one compatible
integer/real basis with a rational H law and an exact full-lattice integer
grid in those very same coordinates, before all original H elements. -/
theorem observation_rational_group_full_lattice_presentation
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ d : ℕ, ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space,
      ∃ Q : (sigma ⊕ Fin d) → MvPolynomial ((sigma ⊕ Fin d) ⊕ (sigma ⊕ Fin d)) ℚ,
        (∀ i, bR i = (bZ i).val) ∧
        (∀ a e : ObservationGroup V, ∀ s,
          observationFullCoordinates V coord bR (a * e) s =
            MvPolynomial.aeval (Sum.elim (observationFullCoordinates V coord bR a)
              (observationFullCoordinates V coord bR e)) (Q s)) ∧
        (∀ a : ObservationGroup V, a ∈ observationLatticeSubgroup V Gamma ↔
          ∃ z : (sigma ⊕ Fin d) → ℤ, observationFullCoordinates V coord bR a = fun s => (z s : ℝ)) := by
  obtain ⟨d, bZ, bR, B, hb, hB⟩ := observation_compatible_rational_bases V Gamma b coord hint hcover P hP
  obtain ⟨Q, hQ⟩ := observation_group_rational_polynomial_presentation V Gamma coord bR hint hcover p hgroup B hB
  exact ⟨d, bZ, bR, Q, hb, hQ, observation_lattice_full_integer_coordinates V Gamma coord hint hcover bZ bR hb⟩

end GMZP0
