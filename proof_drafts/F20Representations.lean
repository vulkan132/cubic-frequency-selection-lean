import GMZP0.PairGeometry
import Mathlib.Data.Int.GCD

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem pair_equal_value_gcd_divisibility (h h' : ℕ) (v w v₀ w₀ : ℤ)
    (he : (h : ℤ) * v + h' * w = h * v₀ + h' * w₀) :
    (h' : ℤ) ∣ (Nat.gcd h h' : ℤ) * (v - v₀) := by
  have hd : (h' : ℤ) ∣ (h : ℤ) * (v - v₀) := by
    refine ⟨w₀ - w, ?_⟩
    nlinarith
  obtain ⟨k, hk⟩ := hd
  refine ⟨k * Nat.gcdA h h' + Nat.gcdB h h' * (v - v₀), ?_⟩
  rw [Nat.gcd_eq_gcd_ab]
  calc
    _ = ((h : ℤ) * (v - v₀)) * Nat.gcdA h h' +
        (h' : ℤ) * Nat.gcdB h h' * (v - v₀) := by ring
    _ = _ := by rw [hk]; ring

theorem pair_representation_code_bound {N s A h' g : ℕ} (hA : 0 < A) (hh' : 0 < h')
    (hs : 2 * s < N) (hlarge : N ≤ A * h') (hg : g ≤ A)
    (δ k : ℤ) (hδ : |δ| ≤ 2 * s) (he : (h' : ℤ) * k = (g : ℤ) * δ) :
    |k| ≤ (A : ℤ) ^ 2 := by
  have ha : (0 : ℤ) < A := by exact_mod_cast hA
  have hh : (0 : ℤ) < h' := by exact_mod_cast hh'
  have hsr : (2 : ℤ) * s < N := by exact_mod_cast hs
  have hl : (N : ℤ) ≤ A * h' := by exact_mod_cast hlarge
  have hgr : (g : ℤ) ≤ A := by exact_mod_cast hg
  have hp : (g : ℤ) * |δ| ≤ (A : ℤ) * (2 * s) :=
    mul_le_mul hgr hδ (abs_nonneg _) (by omega)
  have hab := congrArg abs he
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg h' : (0 : ℤ) ≤ h'),
    abs_of_nonneg (Nat.cast_nonneg g : (0 : ℤ) ≤ g)] at hab
  have h₁ : (A : ℤ) * (2 * s) < (A : ℤ) * N := mul_lt_mul_of_pos_left hsr ha
  have h₂ : (A : ℤ) * N ≤ (A : ℤ) * ((A : ℤ) * h') := mul_le_mul_of_nonneg_left hl ha.le
  nlinarith



theorem integer_pair_representation_count {N s A h h' : ℕ}
    (hA : 0 < A) (hh : 0 < h) (hh' : 0 < h') (hs : 2 * s < N)
    (hlarge : N ≤ A * h') (hg : Nat.gcd h h' ≤ A) (t : ℤ) :
    (Finset.univ.filter (fun v : smoothingShiftLabels s × smoothingShiftLabels s =>
      (h : ℤ) * v.1.val + h' * v.2.val = t)).card ≤ 1 + 2 * A ^ 2 := by
  classical
  let S := Finset.univ.filter (fun v : smoothingShiftLabels s × smoothingShiftLabels s =>
    (h : ℤ) * v.1.val + h' * v.2.val = t)
  change S.card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hS
    have hval (v : smoothingShiftLabels s × smoothingShiftLabels s) (hv : v ∈ S) :
        (h : ℤ) * v.1.val + h' * v.2.val = t := (Finset.mem_filter.mp hv).2
    let code := fun v : smoothingShiftLabels s × smoothingShiftLabels s =>
      ((Nat.gcd h h' : ℤ) * (v.1.val - v₀.1.val)) / (h' : ℤ)
    have hc (v : smoothingShiftLabels s × smoothingShiftLabels s) (hv : v ∈ S) :
        (h' : ℤ) * code v = (Nat.gcd h h' : ℤ) * (v.1.val - v₀.1.val) := by
      dsimp [code]
      rw [mul_comm, Int.ediv_mul_cancel
        (pair_equal_value_gcd_divisibility h h' _ _ _ _ ((hval v hv).trans (hval v₀ hv₀).symm))]
    have hδ (v : smoothingShiftLabels s × smoothingShiftLabels s) :
        |v.1.val - v₀.1.val| ≤ 2 * s := by
      have hv := v.1.property
      have hb := v₀.1.property
      simp only [smoothingShiftLabels, Finset.mem_Icc] at hv hb
      rw [abs_le]
      omega
    have hmaps : Set.MapsTo code (S : Set (smoothingShiftLabels s × smoothingShiftLabels s))
        (Finset.Icc (-(A : ℤ) ^ 2) ((A : ℤ) ^ 2) : Set ℤ) := by
      intro v hv
      apply Finset.mem_Icc.mpr
      have hb := pair_representation_code_bound hA hh' hs hlarge hg _ _ (hδ v) (hc v hv)
      exact abs_le.mp hb
    have hinj : (S : Set (smoothingShiftLabels s × smoothingShiftLabels s)).InjOn code := by
      intro v hv w hw he
      have hgz : (0 : ℤ) < Nat.gcd h h' := by exact_mod_cast Nat.gcd_pos_of_pos_left h' hh
      have hgdelta : (Nat.gcd h h' : ℤ) * (v.1.val - v₀.1.val) =
          (Nat.gcd h h' : ℤ) * (w.1.val - v₀.1.val) := by rw [← hc v hv, ← hc w hw, he]
      have hfirst : v.1 = w.1 := by
        apply Subtype.ext
        have he := mul_left_cancel₀ hgz.ne' hgdelta
        omega
      have hsecond : v.2 = w.2 := by
        apply Subtype.ext
        have heq := (hval v hv).trans (hval w hw).symm
        rw [hfirst] at heq
        have hm : (h' : ℤ) * v.2.val = (h' : ℤ) * w.2.val := by linarith
        exact mul_left_cancel₀ (by exact_mod_cast hh'.ne' : (h' : ℤ) ≠ 0) hm
      exact Prod.ext hfirst hsecond
    have hcard := Finset.card_le_card_of_injOn code hmaps hinj
    have ht : (Finset.Icc (-(A : ℤ) ^ 2) ((A : ℤ) ^ 2)).card = 1 + 2 * A ^ 2 := by
      rw [Int.card_Icc]
      have he : (A : ℤ) ^ 2 + 1 - -(A : ℤ) ^ 2 = ((1 + 2 * A ^ 2 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [he, Int.toNat_natCast]
    simpa only [ht] using hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    omega

end GMZP0
