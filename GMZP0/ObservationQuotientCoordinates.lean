import GMZP0.ObservationIntegerIntersection

/-! Actual adapted bases supply the manuscript's real quotient coefficients.
The coordinate map has kernel exactly W and uses the original lattice representatives.
Quantitative height and degree bounds for rational presentations remain separate. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- An adapted integer basis spans the actual W on its left part when the integer intersection spans W. -/
theorem observation_adapted_left_real_span (V : ObservationModule G) (Gamma : Subgroup G)
    {p q : ℕ} (bW : Basis (Fin p) ℤ (observationIntegerDifferenceModule V Gamma))
    (b : Basis (Fin p ⊕ Fin q) ℤ (observationIntegerLattice V Gamma))
    (hleft : ∀ i, b (Sum.inl i) = (bW i).val)
    (hW : Submodule.span ℝ {F : V.space | F ∈ observationDifferenceSpace V ∧
      F ∈ observationIntegerLattice V Gamma} = observationDifferenceSpace V) :
    Submodule.span ℝ (Set.range (fun i => (b (Sum.inl i)).val)) = observationDifferenceSpace V := by
  classical
  let S := Submodule.span ℝ (Set.range (fun i => (b (Sum.inl i)).val))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (b (Sum.inl i)).val ∈ observationDifferenceSpace V
    rw [hleft]
    exact (bW i).property
  · apply hW.ge.trans
    apply Submodule.span_le.mpr
    rintro F ⟨hFW, hFL⟩
    let FZ : observationIntegerDifferenceModule V Gamma := ⟨⟨F, hFL⟩, hFW⟩
    let inc := (observationIntegerLattice V Gamma).subtype.comp
      (observationIntegerDifferenceModule V Gamma).subtype
    have he := congrArg inc (bW.sum_repr FZ)
    simp only [map_sum, map_smul] at he
    change (∑ i, bW.repr FZ i • (bW i).val.val) = F at he
    rw [← he]
    apply S.sum_mem
    intro i _
    apply (S.restrictScalars ℤ).smul_mem
    rw [← hleft]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- The right coordinates of a real adapted basis, taken as an actual real-linear map. -/
def observationQuotientCoordinates (V : ObservationModule G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℝ V.space) : V.space →ₗ[ℝ] (Fin q → ℝ) where
  toFun F j := b.repr F (Sum.inr j)
  map_add' F H := by ext j; simp
  map_smul' a F := by ext j; simp

/-- The real coordinates read the original observation's actual basis expansion. -/
theorem observationQuotientCoordinates_apply (V : ObservationModule G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℝ V.space) (F : V.space) (j : Fin q) :
    observationQuotientCoordinates V b F j = b.repr F (Sum.inr j) := rfl

/-- Splitting the full real expansion gives the exact W component and original quotient representatives. -/
theorem observation_quotient_coefficient_decomposition (V : ObservationModule G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℝ V.space)
    (hleft : ∀ i, b (Sum.inl i) ∈ observationDifferenceSpace V) (F : V.space) :
    ∃ FW : observationDifferenceSpace V,
      F = FW.val + ∑ j, observationQuotientCoordinates V b F j • b (Sum.inr j) := by
  refine ⟨⟨∑ i, b.repr F (Sum.inl i) • b (Sum.inl i),
    (observationDifferenceSpace V).sum_mem fun i _ =>
      (observationDifferenceSpace V).smul_mem _ (hleft i)⟩, ?_⟩
  have he := b.sum_repr F
  rw [Fintype.sum_sum_type] at he
  exact he.symm

/-- The right-coordinate map kills precisely W when the left basis vectors span the actual W. -/
theorem observation_quotient_coordinates_kernel (V : ObservationModule G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℝ V.space)
    (hW : Submodule.span ℝ (Set.range (fun i => b (Sum.inl i))) = observationDifferenceSpace V) :
    LinearMap.ker (observationQuotientCoordinates V b) = observationDifferenceSpace V := by
  classical
  apply le_antisymm
  · intro F hF
    have hz (j : Fin q) : b.repr F (Sum.inr j) = 0 := congrFun hF j
    have he := b.sum_repr F
    rw [Fintype.sum_sum_type] at he
    simp only [hz, zero_smul, Finset.sum_const_zero, add_zero] at he
    rw [← he, ← hW]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [← hW]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change observationQuotientCoordinates V b (b (Sum.inl i)) = 0
    ext j
    simp [observationQuotientCoordinates]

/-- Every real quotient-coordinate vector is attained by the actual right basis combination. -/
theorem observation_quotient_coordinates_surjective (V : ObservationModule G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℝ V.space) :
    Function.Surjective (observationQuotientCoordinates V b) := by
  classical
  intro a
  refine ⟨∑ j, a j • b (Sum.inr j), ?_⟩
  ext i
  simp [observationQuotientCoordinates, Finsupp.single_apply]

/-- On the original integer subgroup, the extended real coordinates retain their integer values. -/
theorem observation_quotient_coordinates_integral (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] (Gamma : Subgroup G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℤ (observationIntegerLattice V Gamma))
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0)
    (hfull : Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤)
    (F : observationIntegerLattice V Gamma) (j : Fin q) :
    observationQuotientCoordinates V (observationRealBasis V Gamma b hsep hfull) F.val j =
      (b.repr F (Sum.inr j) : ℝ) :=
  observationRealBasis_repr_int V Gamma b hsep hfull F (Sum.inr j)

/-- Every integer quotient-coordinate vector has a representative in the original V_Z. -/
theorem observation_quotient_coordinates_integer_surjective (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] (Gamma : Subgroup G) {p q : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℤ (observationIntegerLattice V Gamma))
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0)
    (hfull : Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤)
    (a : Fin q → ℤ) :
    ∃ F : observationIntegerLattice V Gamma,
      observationQuotientCoordinates V (observationRealBasis V Gamma b hsep hfull) F.val =
        fun j => (a j : ℝ) := by
  classical
  refine ⟨∑ j, a j • b (Sum.inr j), ?_⟩
  ext j
  rw [observation_quotient_coordinates_integral]
  simp [Finsupp.single_apply]

/-- Applying quotient coordinates preserves every finite polynomial expansion in the original variable. -/
theorem observation_quotient_coordinates_polynomial (V : ObservationModule G) {p q D : ℕ}
    (b : Basis (Fin p ⊕ Fin q) ℝ V.space) (A : Fin (D + 1) → V.space) (y : ℝ) (j : Fin q) :
    observationQuotientCoordinates V b (∑ d : Fin (D + 1), y ^ (d : ℕ) • A d) j =
      ∑ d : Fin (D + 1), y ^ (d : ℕ) * observationQuotientCoordinates V b (A d) j := by
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The literal rational presentation supplies compatible actual integer and real adapted bases.
No abstract adapted basis, torsion-free quotient, or integer spanning conclusion is assumed. -/
theorem observation_adapted_bases_of_presentation (V : ObservationModule G) (Gamma : Subgroup G)
    {sigma iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i))
    (hW : RationalInBasis b (observationDifferenceSpace V)) :
    ∃ p q : ℕ, ∃ bZ : Basis (Fin p ⊕ Fin q) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin p ⊕ Fin q) ℝ V.space,
        (∀ i, bR i = (bZ i).val) ∧
        Submodule.span ℝ (Set.range (fun i => bR (Sum.inl i))) = observationDifferenceSpace V ∧
        (∀ (F : observationIntegerLattice V Gamma) i, bR.repr F.val i = (bZ.repr F i : ℝ)) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hsep := observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hb)
  have hfull := observation_integer_span_top V Gamma b coord hint P hb
  let : Module.Finite ℤ (observationIntegerLattice V Gamma) :=
    observation_integer_module_finite V Gamma hsep
  obtain ⟨p, q, bW, _, bZ, hleft, _⟩ := observation_integer_adapted_basis V Gamma
  let bR := observationRealBasis V Gamma bZ hsep hfull
  have happly (i) : bR i = (bZ i).val := observationRealBasis_apply V Gamma bZ hsep hfull i
  refine ⟨p, q, bZ, bR, happly, ?_, ?_⟩
  · simp_rw [happly]
    exact observation_adapted_left_real_span V Gamma bW bZ hleft
      (observation_integer_intersection_real_span V Gamma b coord hint P hb hW)
  · exact observationRealBasis_repr_int V Gamma bZ hsep hfull

/-- A literal rational translation matrix supplies W-rationality internally for the adapted basis construction. -/
theorem observation_adapted_bases_of_matrix (V : ObservationModule G) (Gamma : Subgroup G)
    {sigma iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (hcoord : Function.Surjective coord)
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i))
    (A : iota → iota → MvPolynomial sigma ℚ)
    (hA : ∀ g j i, b.repr (observationTranslate V g (b j) - b j) i =
      MvPolynomial.aeval (coord g) (A i j)) :
    ∃ p q : ℕ, ∃ bZ : Basis (Fin p ⊕ Fin q) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin p ⊕ Fin q) ℝ V.space,
        (∀ i, bR i = (bZ i).val) ∧
        Submodule.span ℝ (Set.range (fun i => bR (Sum.inl i))) = observationDifferenceSpace V ∧
        (∀ (F : observationIntegerLattice V Gamma) i, bR.repr F.val i = (bZ.repr F i : ℝ)) :=
  observation_adapted_bases_of_presentation V Gamma b coord hint hcover P hb
    (observation_difference_rational_of_matrix V b coord hcoord A hA)

end GMZP0
