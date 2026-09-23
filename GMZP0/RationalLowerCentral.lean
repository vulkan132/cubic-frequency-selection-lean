import GMZP0.RationalLieBracket
import GMZP0.RationalSpanBasis

/-! Finite rational generators for every actual lower-central Lie ideal,
recursively derived from the actual bracket tensor in one fixed basis. -/
noncomputable section
open Module
namespace GMZP0
variable {L iota : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype iota]

/-- The rational coordinate vector of a basis element is the corresponding unit vector. -/
theorem rational_basis_vector_single [DecidableEq iota] (b : Basis iota ℝ L) (i : iota) :
    rationalBasisVector b (Pi.single i (1 : ℚ)) = b i := by
  classical
  simp [rationalBasisVector, Pi.single_apply, apply_ite]

/-- Zero denotes the whole Lie algebra; each successor brackets with
every original basis vector, in the convention of Mathlib's lower series. -/
def rationalLowerCentralGenerators (C : iota → iota → iota → ℚ) : ℕ → Finset (iota → ℚ)
  | 0 => by classical exact Finset.univ.image (fun i => Pi.single i (1 : ℚ))
  | n + 1 => rationalBasisBracketStep C (rationalLowerCentralGenerators C n)

/-- The initial generator list has exactly the original basis as image. -/
theorem rational_lower_central_zero_image (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ) :
    rationalBasisVector b '' (rationalLowerCentralGenerators C 0 : Set (iota → ℚ)) = Set.range b := by
  classical
  ext x
  simp [rationalLowerCentralGenerators, rational_basis_vector_single]

/-- The recursively constructed rational generators span the actual
Mathlib lower-central Lie ideal, at every depth and in the same basis. -/
theorem rational_lower_central_span (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ)
    (hC : ∀ i j k, b.repr ⁅b i, b j⁆ k = (C i j k : ℝ)) (n : ℕ) :
    (LieModule.lowerCentralSeries ℝ L L n).toSubmodule =
      Submodule.span ℝ (rationalBasisVector b '' (rationalLowerCentralGenerators C n : Set (iota → ℚ))) := by
  induction n with
  | zero => rw [rational_lower_central_zero_image, b.span_eq]; rfl
  | succ n ih =>
    rw [LieModule.lowerCentralSeries_succ]
    exact rational_lie_ideal_step b C hC _ _ ih

/-- Every actual lower-central Lie ideal is rational in the original basis. -/
theorem rational_lower_central_in_basis (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ)
    (hC : ∀ i j k, b.repr ⁅b i, b j⁆ k = (C i j k : ℝ)) (n : ℕ) :
    RationalInBasis b (LieModule.lowerCentralSeries ℝ L L n).toSubmodule :=
  ⟨rationalLowerCentralGenerators C n, rational_lower_central_span b C hC n⟩

/-- For each fixed finite filtration length, one height bound precedes
every layer, every listed rational generator and every coordinate. -/
theorem rational_lower_central_generator_heights
    (C : iota → iota → iota → ℚ) (r : ℕ) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ n ≤ r, ∀ a ∈ rationalLowerCentralGenerators C n,
      ∀ i, rationalHeight (a i) ≤ Q := by
  classical
  let H := (Finset.range (r + 1)).sup
    (fun n => (rationalLowerCentralGenerators C n).sup rationalArrayHeight)
  refine ⟨max 3 H, lt_of_lt_of_le (by decide : 2 < (3 : ℕ)) (le_max_left _ _), ?_⟩
  intro n hn a ha i
  have hinner := Finset.le_sup (f := rationalArrayHeight) ha
  have houter := Finset.le_sup
    (f := fun n => (rationalLowerCentralGenerators C n).sup rationalArrayHeight)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  exact (rational_array_height_bound a i).trans (hinner.trans (houter.trans (le_max_right _ _)))

/-- A common height bound for any fixed finite number of lower-central
layers applies to actual bases selected from their original generators. -/
theorem rational_lower_central_bounded_bases (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ)
    (hC : ∀ i j k, b.repr ⁅b i, b j⁆ k = (C i j k : ℝ)) (r : ℕ) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ n ≤ r,
      ∃ J : Set L, J.Finite ∧
        ∃ bN : Basis J ℝ (LieModule.lowerCentralSeries ℝ L L n).toSubmodule,
          ∀ j : J, ∃ a : iota → ℚ, ∀ i,
            b.repr (bN j : L) i = (a i : ℝ) ∧ rationalHeight (a i) ≤ Q := by
  obtain ⟨Q, hQ, hheight⟩ := rational_lower_central_generator_heights C r
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  exact rational_span_bounded_basis b _ (rationalLowerCentralGenerators C n)
    (rational_lower_central_span b C hC n) Q (hheight n hn)

end GMZP0
