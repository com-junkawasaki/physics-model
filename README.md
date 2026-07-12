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

Run:

```sh
lake build
lake exe physics-model
```

## Open physics obligations

1. extend the checked homogeneous scalar continuum certificate to a
   four-dimensional tensor geometry with controlled coarse graining;
2. construct the nonabelian Standard Model representations, couplings, chirality,
   and symmetry breaking from microscopic modes (the rational hypercharge anomaly
   sums are now checked);
3. recover Lorentz symmetry and unitary scattering;
4. derive amplitude selection and normalization from relational dynamics (the
   finite norm-square probability calculus itself is now checked);
5. explain black-hole thermodynamics and evaporation;
6. produce falsifiable cosmological predictions;
7. construct clock equivalences for realistic interacting quantum clocks.
