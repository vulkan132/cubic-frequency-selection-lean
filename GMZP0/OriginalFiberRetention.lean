import GMZP0.CyclicOriginalFields
import GMZP0.OriginalWeights

/-! Transfer selected cyclic fibres back to actual original base points.
The selected subsets and matching functions are explicit inputs; no structural
existence or nilpolynomial property is asserted by these transport results. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def retainedOriginalFibers (N q : ℕ) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q)) : Finset (Base N) :=
  Finset.univ.filter (fun z => z.1 ∈ H ∧ cyclicRow N q z.2 ∈ S z.1)

theorem cyclic_nonzero_weight_in_original_range {N q : ℕ} [NeZero q] (hq : N ^ 2 < q)
    (σ : Base N → ℝ) (x : Fin N) (Y : ZMod q) (hσ : cyclicField N q σ 0 x Y ≠ 0) :
    Y ∈ Set.range (cyclicRow N q) := by
  by_contra hn
  exact hσ (cyclicField_outside_range hq σ 0 x Y hn)

theorem cyclic_row_preimage_card {N q : ℕ} (hq : N ^ 2 < q)
    (S : Finset (ZMod q)) (hS : ∀ Y ∈ S, Y ∈ Set.range (cyclicRow N q)) :
    (Finset.univ.filter (fun y : Fin (N ^ 2) => cyclicRow N q y ∈ S)).card = S.card := by
  classical
  apply Finset.card_bij (fun y _ => cyclicRow N q y)
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · intro y _ z _ he
    exact cyclicRow_injective hq he
  · intro Y hY
    obtain ⟨y, hy⟩ := hS Y hY
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hy]⟩, hy⟩

theorem retainedOriginalFibers_card {N q : ℕ} (hq : N ^ 2 < q)
    (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, Y ∈ Set.range (cyclicRow N q)) :
    (retainedOriginalFibers N q H S).card = ∑ x ∈ H, (S x).card := by
  classical
  have he : (retainedOriginalFibers N q H S).card =
      ∑ x ∈ H, (Finset.univ.filter (fun y : Fin (N ^ 2) => cyclicRow N q y ∈ S x)).card := by
    simp only [retainedOriginalFibers, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type, ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_filter]
    exact Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
  rw [he]
  exact Finset.sum_congr rfl (fun x hx => cyclic_row_preimage_card hq (S x) (hS x hx))

theorem retainedOriginalFibers_support {N q : ℕ} (hq : N ^ 2 < q)
    (μ : Base N → ℝ) (D : Finset (Base N)) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (τ : ℝ) (hτ : 0 < τ)
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, τ ≤ cyclicField N q (originalScaledWeight N μ D) 0 x Y)
    (z : Base N) (hz : z ∈ retainedOriginalFibers N q H S) : z ∈ D ∧ μ z ≠ 0 := by
  have hs := (Finset.mem_filter.mp hz).2
  have ht := hS z.1 hs.1 _ hs.2
  rw [cyclicField_original hq] at ht
  exact originalScaledWeight_support μ D z (hτ.trans_le ht).ne'

theorem retainedOriginalFibers_weight_lower {N q : ℕ} (hN : 0 < N) (hq : N ^ 2 < q)
    (μ : Base N → ℝ) (D : Finset (Base N)) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (τ : ℝ) (hτ : 0 < τ)
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, τ ≤ cyclicField N q (originalScaledWeight N μ D) 0 x Y)
    (z : Base N) (hz : z ∈ retainedOriginalFibers N q H S) : τ / (N : ℝ) ^ 3 ≤ μ z := by
  have hs := (Finset.mem_filter.mp hz).2
  have hd := (retainedOriginalFibers_support hq μ D H S τ hτ hS z hz).1
  have ht := hS z.1 hs.1 _ hs.2
  rw [cyclicField_original hq, originalScaledWeight, if_pos hd] at ht
  change τ ≤ (N : ℝ) ^ 3 * μ z at ht
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ (pow_pos hn 3)).mpr
  simpa only [mul_comm] using ht

theorem retainedOriginalFibers_mass {N q : ℕ} [NeZero q] (hN : 0 < N) (hq : N ^ 2 < q)
    (μ : Base N → ℝ) (D : Finset (Base N)) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (τ cModel : ℝ) (hτ : 0 < τ)
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, τ ≤ cyclicField N q (originalScaledWeight N μ D) 0 x Y)
    (hcard : ∀ x ∈ H, cModel * q ≤ (S x).card) :
    (H.card : ℝ) * cModel * q * τ / (N : ℝ) ^ 3 ≤ ∑ z ∈ retainedOriginalFibers N q H S, μ z := by
  classical
  have hRange : ∀ x ∈ H, ∀ Y ∈ S x, Y ∈ Set.range (cyclicRow N q) := by
    intro x hx Y hY
    exact cyclic_nonzero_weight_in_original_range hq _ x Y (hτ.trans_le (hS x hx Y hY)).ne'
  have hc : (H.card : ℝ) * cModel * q ≤ (retainedOriginalFibers N q H S).card := by
    rw [retainedOriginalFibers_card hq H S hRange, Nat.cast_sum]
    have he := Finset.sum_le_sum hcard
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using he
  have hm := Finset.sum_le_sum (fun z hz => retainedOriginalFibers_weight_lower hN hq μ D H S τ hτ hS z hz)
  simp only [Finset.sum_const, nsmul_eq_mul] at hm
  have hmul := mul_le_mul_of_nonneg_right hc (show 0 ≤ τ / (N : ℝ) ^ 3 by positivity)
  calc
    _ = ((H.card : ℝ) * cModel * q) * (τ / (N : ℝ) ^ 3) := by ring
    _ ≤ _ := hmul.trans hm

theorem retainedOriginalFibers_circle_error {N q : ℕ} (hq : N ^ 2 < q)
    (μ : Base N → ℝ) (D : Finset (Base N)) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (τ : ℝ) (hτ : 0 < τ)
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, τ ≤ cyclicField N q (originalScaledWeight N μ D) 0 x Y)
    (θ : Base N → Frequency) (F G : Fin N → ZMod q → ℝ) (d : ℕ) (ε : ℝ)
    (herror : ∀ x Y, 0 < cyclicField N q (originalScaledWeight N μ D) 0 x Y →
      ‖((F x Y : ℝ) : Frequency) - d • cyclicField N q θ 0 x Y‖ ≤ ε)
    (hmodel : ∀ x ∈ H, ∀ Y ∈ S x, F x Y = G x Y)
    (z : Base N) (hz : z ∈ retainedOriginalFibers N q H S) :
    ‖d • θ z - ((G z.1 (cyclicRow N q z.2) : ℝ) : Frequency)‖ ≤ ε := by
  have hs := (Finset.mem_filter.mp hz).2
  have he := herror z.1 _ (hτ.trans_le (hS z.1 hs.1 _ hs.2))
  rw [cyclicField_original hq, hmodel z.1 hs.1 _ hs.2] at he
  simpa only [norm_sub_rev] using he

theorem retainedOriginalFibers_uniform_mass {N q : ℕ} [NeZero q]
    (hN : 0 < N) (hq : N ^ 2 < q) (hqScale : 64 * N ^ 2 ≤ q)
    (μ : Base N → ℝ) (D : Finset (Base N)) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (ρ τ cModel : ℝ) (hρ : 0 ≤ ρ) (hτ : 0 < τ) (hcModel : 0 ≤ cModel)
    (hH : ρ * N ≤ H.card)
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, τ ≤ cyclicField N q (originalScaledWeight N μ D) 0 x Y)
    (hcard : ∀ x ∈ H, cModel * q ≤ (S x).card) :
    64 * ρ * cModel * τ ≤ ∑ z ∈ retainedOriginalFibers N q H S, μ z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : 64 * (N : ℝ) ^ 2 ≤ q := by exact_mod_cast hqScale
  have hlower : 64 * ρ * cModel * τ ≤ (H.card : ℝ) * cModel * q * τ / (N : ℝ) ^ 3 := by
    apply (le_div_iff₀ (pow_pos hn 3)).mpr
    calc
      _ = (ρ * N) * cModel * (64 * (N : ℝ) ^ 2) * τ := by ring
      _ ≤ (ρ * N) * cModel * q * τ := by gcongr
      _ ≤ (H.card : ℝ) * cModel * q * τ := by gcongr
  exact hlower.trans (retainedOriginalFibers_mass hN hq μ D H S τ cModel hτ hS hcard)

theorem retainedOriginalFibers_original_response {N q : ℕ} (hq : N ^ 2 < q)
    (μ : Base N → ℝ) (D : Finset (Base N)) (H : Finset (Fin N)) (S : Fin N → Finset (ZMod q))
    (τ : ℝ) (hτ : 0 < τ)
    (hS : ∀ x ∈ H, ∀ Y ∈ S x, τ ≤ cyclicField N q (originalScaledWeight N μ D) 0 x Y)
    (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (η : ℝ)
    (hresponse : ∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re)
    (z : Base N) (hz : z ∈ retainedOriginalFibers N q H S) :
    η ≤ (lam z * response N f z (θ z)).re := by
  have hs := retainedOriginalFibers_support hq μ D H S τ hτ hS z hz
  exact hresponse z hs.1 hs.2

end GMZP0
