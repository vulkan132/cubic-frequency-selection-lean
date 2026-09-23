import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Reduced rational heights and finite coefficient universes. Bounds
on a fixed finite presentation precede all runtime real coefficients;
uniformity over varying presentations requires an actual height bound. -/
noncomputable section
namespace GMZP0

/-- Height in reduced form, as in Green--Tao Definition 2.3. -/
def rationalHeight (a : ℚ) : ℕ := max a.num.natAbs a.den

/-- Height bounds control both the reduced numerator and denominator. -/
theorem rational_height_le_iff (a : ℚ) (H : ℕ) :
    rationalHeight a ≤ H ↔ a.num.natAbs ≤ H ∧ a.den ≤ H := max_le_iff

/-- One explicit bound for an entire finite rational coefficient array. -/
def rationalArrayHeight {iota : Type*} [Fintype iota] (a : iota → ℚ) : ℕ :=
  max 1 (Finset.univ.sup fun i => rationalHeight (a i))

/-- The common height of a finite rational array bounds every entry. -/
theorem rational_array_height_bound {iota : Type*} [Fintype iota]
    (a : iota → ℚ) (i : iota) : rationalHeight (a i) ≤ rationalArrayHeight a := by
  exact (Finset.le_sup (f := fun j => rationalHeight (a j)) (Finset.mem_univ i)).trans
    (le_max_right _ _)

/-- Bounded reduced height gives a genuinely finite rational universe,
proved by an explicit numerator/denominator grid. -/
theorem bounded_rational_height_finite (H : ℕ) :
    {a : ℚ | rationalHeight a ≤ H}.Finite := by
  classical
  let S := (Finset.Icc (-(H : ℤ)) (H : ℤ)).product (Finset.Icc 1 H)
  apply (S.image (fun z : ℤ × ℕ => (z.1 : ℚ) / (z.2 : ℚ))).finite_toSet.subset
  intro a ha
  obtain ⟨hn, hd⟩ := (rational_height_le_iff a H).mp ha
  have hn' : |a.num| ≤ (H : ℤ) := by
    have hh : (a.num.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using hh
  apply Finset.mem_image.mpr
  refine ⟨(a.num, a.den), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hn'),
      Finset.mem_Icc.mpr ⟨a.den_pos, hd⟩⟩
  · exact a.num_div_den

/-- The full set of height-bounded rational coordinate vectors is finite. -/
theorem bounded_rational_vectors_finite {iota : Type*} [Finite iota] (H : ℕ) :
    {a : iota → ℚ | ∀ i, rationalHeight (a i) ≤ H}.Finite :=
  Set.Finite.pi' fun _ => bounded_rational_height_finite H

/-- A fixed transformation of bounded-height rational presentations has
a common finite output-height bound. This requires the input-height
bound and says nothing about unrestricted real observation coefficients. -/
theorem bounded_rational_outputs_uniform {iota tau : Type*}
    [Finite iota] [Fintype tau] (F : (iota → ℚ) → tau → ℚ) (H : ℕ) :
    ∃ M : ℕ, ∀ a : iota → ℚ, (∀ i, rationalHeight (a i) ≤ H) →
      ∀ j, rationalHeight (F a j) ≤ M := by
  classical
  let S := (bounded_rational_vectors_finite (iota := iota) H).toFinset
  refine ⟨S.sup (fun a => rationalArrayHeight (F a)), ?_⟩
  intro a ha j
  have hmem : a ∈ S := (bounded_rational_vectors_finite H).mem_toFinset.mpr ha
  exact (rational_array_height_bound (F a) j).trans
    (Finset.le_sup (f := fun a => rationalArrayHeight (F a)) hmem)

end GMZP0
