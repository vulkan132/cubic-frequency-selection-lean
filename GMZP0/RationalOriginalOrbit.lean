import GMZP0.ObservationIntegerRationalBasis
import GMZP0.PolynomialOriginalOrbit

/-! The original rational basis data suffice for the full original orbit
theorem. Its compatible actual integer/real bases are now constructed. -/
noncomputable section
open Set Metric Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
universe uI

/-- Mapping rational coefficients into R preserves the literal value at
every unrestricted real coordinate vector. -/
theorem rational_polynomial_real_map_eval {sigma : Type*}
    (P : MvPolynomial sigma ℚ) (x : sigma → ℝ) :
    MvPolynomial.aeval x (P.map (algebraMap ℚ ℝ)) = MvPolynomial.aeval x P := by
  rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map]
  rfl

variable {G iota : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Fintype iota] {m : ℕ}

/-- The original rational group/basis presentation constructs the full
metric and lattice-basis geometry. The metric precedes sections and all
real observation data, and the original full N normalization is retained. -/
theorem original_rational_boundary_nonequidistribution
    (V : ObservationModule G) (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u s, coord (g * u) s = coord u s + MvPolynomial.aeval (coord u) (q g s))
    (hlow : ∀ g s d, d ∈ (q g s).support → ∀ j ∈ d.support, j.val < s.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hgrid : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (b : Basis iota ℝ V.space) (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (a : Fin m → ℝ) :
    ∃ mQ : MetricSpace (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
      mQ.toUniformSpace.toTopologicalSpace =
        QuotientGroup.instTopologicalSpace (observationLatticeSubgroup V Gamma) ∧
      (letI := mQ
       ∀ (c : ObservationSection Gamma),
         Set.range c.representative ⊆ coordinateHalfOpenCell coord a →
       ∀ (mu : Measure (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma))
         [IsProbabilityMeasure mu] [SMulInvariantMeasure (ObservationGroup V) _ mu],
       ∀ (nu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure nu] [SMulInvariantMeasure G _ nu],
       ∀ gamma : ℝ, 0 < gamma →
         ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
           (∀ (I : Type uI) [Fintype I]
             (u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma),
             gamma < ‖complexUniformMean (fun i => quotientObservation V c (u i))‖ →
               ¬ LipschitzOrbitDiscrepancy mu u alpha) ∧
           (∀ N : ℕ, 0 < N → ∀ (I : Type uI) [Fintype I], Fintype.card I ≤ N →
             ∀ u : I → ObservationGroup V ⧸ observationLatticeSubgroup V Gamma,
               gamma < ‖(∑ i, quotientObservation V c (u i)) / (N : ℂ)‖ →
                 gamma * (N : ℝ) < Fintype.card I ∧ ¬ LipschitzOrbitDiscrepancy mu u alpha)) := by
  obtain ⟨d, bZ, bR, Q, hb, hQ⟩ :=
    observation_compatible_rational_bases V Gamma b coord hint hgrid P hP
  apply original_polynomial_boundary_nonequidistribution V Gamma coord
    (fun s => (p s).map (algebraMap ℚ ℝ)) _ q htri hlow hint hgrid
    bZ bR hb (fun i => (Q i).map (algebraMap ℚ ℝ)) _ h1 a
  · intro g h s
    rw [rational_polynomial_real_map_eval]
    exact hjoint g h s
  · intro j g
    rw [rational_polynomial_real_map_eval]
    exact hQ j g

end GMZP0
