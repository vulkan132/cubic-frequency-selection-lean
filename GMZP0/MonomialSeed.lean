import GMZP0.MonomialInterpolation

/-! Actual bounded clusters and uniform integer-multiplier seeds for dense monomial returns. -/
noncomputable section
namespace GMZP0

/-- A bucket containing D+1 distinct original integers gives a bounded relative node pattern. -/
theorem bounded_integer_cluster {N L : ℕ} (hL : 0 < L) (D : ℕ) (S : Finset ℤ)
    (hS : S ⊆ Finset.Icc (-(N : ℤ)) N) (hcard : (2 * N / L + 1) * D < S.card) :
    ∃ H : ℤ, ∃ v : Fin (D + 1) → Fin L, Function.Injective v ∧
      ∀ i, H + (v i : ℤ) ∈ S := by
  classical
  let bucket (h : ℤ) : ℕ := (h + N).toNat / L
  have hm : ∀ h ∈ S, bucket h ∈ Finset.range (2 * N / L + 1) := by
    intro h hh
    have hi := Finset.mem_Icc.mp (hS hh)
    have hb : (h + (N : ℤ)).toNat ≤ 2 * N := by omega
    have hd := Nat.div_le_div_right (c := L) hb
    simp only [bucket, Finset.mem_range]
    omega
  have hc : (Finset.range (2 * N / L + 1)).card * D < S.card := by simpa using hcard
  obtain ⟨b, _, hb⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hm hc
  let F := S.filter (fun h => bucket h = b)
  obtain ⟨T, hTF, hTc⟩ := Finset.exists_subset_card_eq (show D + 1 ≤ F.card from hb)
  have hTS : T ⊆ S := hTF.trans (Finset.filter_subset _ _)
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  let e : T ≃ Fin (D + 1) := Fintype.equivFinOfCardEq (by simpa using hTc)
  let z (i : Fin (D + 1)) : ℤ := (e.symm i).val
  let H := T.min' hT
  have hzm (i : Fin (D + 1)) : z i ∈ T := (e.symm i).property
  have hHm : H ∈ T := T.min'_mem hT
  have hmin (i : Fin (D + 1)) : H ≤ z i := T.min'_le _ (hzm i)
  have hgap (i : Fin (D + 1)) : z i - H < (L : ℤ) := by
    have hzi := Finset.mem_Icc.mp (hS (hTS (hzm i)))
    have hHi := Finset.mem_Icc.mp (hS (hTS hHm))
    have hzb := (Finset.mem_filter.mp (hTF (hzm i))).2
    have hHb := (Finset.mem_filter.mp (hTF hHm)).2
    have he : (z i + (N : ℤ)).toNat / L = (H + (N : ℤ)).toNat / L := hzb.trans hHb.symm
    have hzmod := Nat.mod_lt (z i + (N : ℤ)).toNat hL
    have hHmod := Nat.mod_lt (H + (N : ℤ)).toNat hL
    have hzdiv := Nat.mod_add_div (z i + (N : ℤ)).toNat L
    have hHdiv := Nat.mod_add_div (H + (N : ℤ)).toNat L
    rw [he] at hzdiv
    omega
  let v (i : Fin (D + 1)) : Fin L := ⟨(z i - H).toNat, by have := hgap i; omega⟩
  have he (i : Fin (D + 1)) : H + (v i : ℤ) = z i := by
    dsimp only [v]
    have := hmin i
    omega
  refine ⟨H, v, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    change z i = z j
    rw [← he i, ← he j, hij]
  · intro i
    rw [he i]
    exact hTS (hzm i)

/-- The cluster cardinality condition has constants before N and the retained set. -/
theorem dense_monomial_cluster_card {N L D : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hL : 8 * ((D : ℝ) + 1) ≤ (L : ℝ) * ρ)
    (hN : 4 * ((D : ℝ) + 1) ≤ (N : ℝ) * ρ)
    (S : Finset ℤ) (hS : (N : ℝ) * ρ ≤ S.card) :
    (2 * N / L + 1) * D < S.card := by
  have hd : ((2 * N / L : ℕ) : ℝ) * (L : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (2 * N) L
  have h1 := mul_le_mul_of_nonneg_right hd hρ
  have h2 := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (2 * N / L) : (0 : ℝ) ≤ (2 * N / L : ℕ))
  have hr : (((2 * N / L : ℕ) : ℝ) + 1) * (D : ℝ) < (S.card : ℝ) := by nlinarith
  exact_mod_cast hr

/-- The seed multiplier and scale threshold are uniform before the original data and error.
Only actual returns in the selected cluster enter the integer combination. -/
theorem uniform_monomial_seed (D : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ a : Frequency, ∀ ε : ℝ, 0 ≤ ε → ∀ S : Finset ℤ,
        S ⊆ Finset.Icc (-(N : ℤ)) N → ρ * (N : ℝ) ≤ S.card →
        (∀ h ∈ S, ‖(h ^ D) • a‖ ≤ ε) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ (Q : ℝ) * ε := by
  let L : ℕ := Nat.ceil (8 * ((D : ℝ) + 1) / ρ)
  let N₀ : ℕ := Nat.ceil (4 * ((D : ℝ) + 1) / ρ) + 1
  have hL : 0 < L := by
    have hh : (0 : ℝ) < L := (by positivity : 0 < 8 * ((D : ℝ) + 1) / ρ).trans_le (Nat.le_ceil _)
    exact_mod_cast hh
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  obtain ⟨Q, hQ, hpattern⟩ := uniform_monomial_pattern_seed D L
  refine ⟨Q, N₀, hQ, hN₀, ?_⟩
  intro N hN a ε hε S hS hd hr
  have hLB : 8 * ((D : ℝ) + 1) ≤ (L : ℝ) * ρ := (div_le_iff₀ hρ).mp (Nat.le_ceil _)
  have hNB : 4 * ((D : ℝ) + 1) ≤ (N : ℝ) * ρ := by
    have hc : Nat.ceil (4 * ((D : ℝ) + 1) / ρ) ≤ N := by dsimp [N₀] at hN; omega
    exact (div_le_iff₀ hρ).mp ((Nat.le_ceil _).trans (by exact_mod_cast hc))
  have hcard := dense_monomial_cluster_card hρ.le hLB hNB S (by simpa only [mul_comm] using hd)
  obtain ⟨H, v, hv, hvs⟩ := bounded_integer_cluster hL D S hS hcard
  exact hpattern v hv H a ε hε (fun i => hr _ (hvs i))

end GMZP0
