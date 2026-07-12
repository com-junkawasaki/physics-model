# physics-model

Lean 4 formalization of a **relational resonance physics model**, assembled from
the local `inc`, `time`, and `inc-rqm` projects.

The checked result is precise but intentionally limited: Lean proves consequences
of the stated background-free, relational, coarse-graining, resonance, and thermal
axioms. It does **not** claim that those axioms derive general relativity, the
Standard Model, the Born rule, or experimental quantum gravity. Those are listed
as open physical obligations rather than hidden as theorems.

## Checked layers

- constraint-selected whole state (`C ψ = 0` abstraction)
- Page--Wootters-style conditional propositions
- invariance under an explicitly certified change of internal clock
- non-embedded labelled relation graphs and sound coarse graining
- stable (`Γ = 0`) versus resonant (`Γ > 0`) reproducible modes
- complex-pole imaginary-part theorems
- relational causal time and entropy-arrow agreement
- reuse of Inc--RQM gauge-invariant relative records
- reuse of Inc cell-gluing cancellation
- normalized finite Born probabilities, bounds, and global-phase invariance
- gauge-invariant Inc--RQM two-path Born intensity
- effective Einstein equation from a certified zero continuum residual
- abstract gauge-matter action invariance, including composed transformations
- machine-checkable Standard-Model certificate boundary (group identification,
  three generations, anomaly cancellation)
- concrete local U(1) frame action on Inc--RQM AB link fields
- explicit two-detector amplitudes `(1 ± u)/2` with probabilities summing to one
- Wilson plaquette density converges to Maxwell density `F²/2` under dyadic refinement
- microscopic residual convergence implies the effective Einstein-sector equation
- checked homogeneous scalar matter--geometry example connecting those two limits
- exact one-generation gravitational, `U(1)³`, `SU(2)²U(1)`, and `SU(3)²U(1)`
  anomaly cancellation
- Lorentz-boost invariance of the `E²-p²` mass shell
- resonance mass-shell preservation under certified boosts
- explicit balanced two-channel S-matrix with exact Born-probability conservation
- complex abelian Higgs potential: positivity, gauge invariance, vacuum radius,
  nonzero vacuum, phase degeneracy, and global minimality
- 3+1-dimensional Minkowski norm and relativistic dispersion invariance under
  longitudinal Lorentz boosts
- exact three-color, weak-doublet, and three-generation multiplicities
- Standard Model electric charges, neutral Higgs vacuum, and all quark/lepton
  Yukawa hypercharge selection rules
- rank-two `4×4` real Einstein-sector tensors with componentwise field equations
  derived from microscopic residual convergence
- preservation of metric, Einstein-tensor, and stress-energy symmetry
- actual `specialUnitaryGroup (Fin 2) ℂ` and `(Fin 3)` fundamental matrix actions
- composition, identity, determinant-one, and Hermitian-norm preservation for
  Higgs doublets and color triplets
- explicit antisymmetric weak tensor `ε`, its identity `UᵀεU = ε`, and
  SU(2)-invariant Yukawa doublet contractions
- nonabelian lattice links, local frame transformations, covariant matter
  transport and finite differences, triangle holonomy, and gauge-invariant flatness
- gauge-invariant nonabelian Wilson trace/action and an SU(2)-doublet Higgs radial potential
- explicit four-index connection curvature, Ricci contraction, scalar curvature,
  and Einstein tensor over `Fin 4`
- Riemann last-index antisymmetry and a fully checked flat-vacuum Einstein sector
- first algebraic Bianchi identity for torsion-free connections
- stress-energy conservation from the Einstein equation, contracted Bianchi
  condition, metric compatibility, and nonzero gravitational coupling

Run:

```sh
lake build
lake exe physics-model
```

## Open physics obligations

1. construct a controlled coarse-graining map feeding the now-checked metric,
   connection, Riemann, Ricci, and four-dimensional Einstein tensor pipeline;
2. construct explicit nonabelian matrix group actions, running couplings,
   chirality, and full electroweak symmetry breaking from microscopic modes
   (representation dimensions, charges, Yukawa hypercharges, anomaly sums, and
   the abelian Higgs vacuum mechanism are now checked);
3. extend the checked 3+1-dimensional axis-boost mass shell and two-channel
   unitary scattering to arbitrary Lorentz transformations and interacting fields;
4. derive amplitude selection and normalization from relational dynamics (the
   finite norm-square probability calculus itself is now checked);
5. explain black-hole thermodynamics and evaporation;
6. produce falsifiable cosmological predictions;
7. construct clock equivalences for realistic interacting quantum clocks.
