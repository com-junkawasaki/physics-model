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
- component covariant derivative `∇_λT_{μν}`, inverse-metric contraction, and
  concrete linear divergence operator
- derived flat-space contracted Bianchi identity and component stress-energy conservation
- Schwarzschild radius, horizon area, Bekenstein--Hawking entropy, Hawking
  temperature, first law, negative evaporation/entropy rates, and `M³` lifetime scaling
- slow-roll scalar/tensor power spectra, positivity, pivot normalization,
  spectral tilts, `r=16ε`, and the falsifiable consistency relation `r=-8n_t`
- homogeneous nonabelian curvature `F=[A,A]`, adjoint covariance, Jacobi identity,
  and the differential/second Yang--Mills Bianchi identity `D_[λ F_{μν]}=0`
- reversible internal-clock isomorphisms with identity, inverse, composition,
  round-trip invariance, and prediction-independent clock reparametrization
- finite-accuracy probabilistic clock changes, additive backreaction-error bounds,
  and recovery of exact prediction equality at zero error
- concrete convex clock-noise/backreaction model `pδ=(1-δ)p+δq` with the
  derived uniform prediction bound `|pδ-p|≤δ`
- full rank-(1,3) Riemann covariant derivative and the differential/second
  Bianchi identity derived in normal coordinates from commuting second derivatives
- double contraction of the differential Bianchi identity, proving
  `∇^μR_{μν}=½∇_νR` and `∇^μG_{μν}=0`
- componentwise differentiated Einstein equation implies `∇^μT_{μν}=0` for
  nonzero gravitational coupling
- finite relational-chart Gram metric, symmetry and diagonal positivity,
  Levi--Civita connection, torsion freedom, curvature, and Einstein-sector assembly
- binary node refinement with split weights and exact coarse-metric preservation
- nodewise approximate-refinement certificates, explicit metric error bounds, and componentwise metric convergence
- explicit propagation of inverse-metric and first-derivative errors to Levi--Civita connection coefficients
- four-dimensional propagation of connection and connection-derivative errors to Riemann curvature
- explicit Riemann-to-Ricci, scalar-curvature, and Einstein-tensor refinement error bounds
- quantitative stability of the full `G + Λg - κT` field-equation residual
- uniform sixteen-component residual convergence implies the full effective Einstein equation
- arbitrary invertible `3+1` Lorentz transformations preserving the Minkowski bilinear form,
  closed under identity, composition, and inverse, with general mass-shell invariance
- Lorentz-covariant finite multiparticle momentum conservation and `2→2` Mandelstam
  invariants `s,t,u`, including invariant amplitudes depending only on those invariants
- finite symmetric-branch derivation of rational Born weights `m/n`, additive coarse-event
  probabilities, complementary normalization, and equality with squared amplitudes
- continuity-and-density uniqueness of the Born response on `[0,1]`, extending rational
  branch weights to every component of an arbitrary normalized finite complex amplitude
- electroweak Higgs neutral mass operator, massless photon kernel, massive `Z` eigenvector,
  nonnegative `W/Z` masses, tree-level mass relation, and surviving electric generator
- abstract gamma-five involution with complementary left/right chiral projectors,
  idempotence, mutual annihilation, completeness, and chirality eigenvalue theorems
- exact one-loop inverse-coupling RG solution, squared-coupling beta function,
  asymptotic-freedom monotonicity, arbitrary weakening, and finite Landau-pole time
- exact Standard Model one-loop beta numerators from particle content:
  `SU(3)=7`, `SU(2)=19/6`, `U(1)=-41/6`, with the corresponding UV/IR sign classification
- bundled proof witness combining the checked Standard Model dimensions,
  Yukawa selection rules, anomaly cancellation, electroweak breaking, and RG pattern
- independent two-particle scattering composition with exact probability conservation
- finite-family multiparticle unitarity and Lorentz-invariant `s,t,u` scattering weights
- finite families of general `n→m` scattering processes with conserved total four-momentum
- frame-invariant Born measurements for finite families of processes under scalar amplitudes
- channel-wise phase twists that preserve family Born normalization and probabilities

Run:

```sh
lake build
lake exe physics-model
```

## Open physics obligations

1. construct a controlled coarse-graining map feeding the now-checked metric,
   connection, Riemann, Ricci, and four-dimensional Einstein tensor pipeline;
2. derive the now-checked one-loop coefficients, bundled Standard Model algebra,
   running-coupling/chiral/electroweak algebra, and its particle assignments from
   microscopic modes (matrix group actions, representation dimensions, charges,
   Yukawa rules, anomaly sums, the Higgs vacuum, photon kernel, and `W/Z` tree-level
   mass relations are checked);
3. derive interacting field dynamics and nontrivial multiparticle unitarity beyond
   the now-checked Lorentz-covariant finite-particle kinematics, `2→2` invariant amplitudes,
   independent two-particle scattering composition, and finite-family Lorentz-invariant
   scattering weights, including finite families of general `n→m` processes and
   frame-invariant Born measurements with channel-wise phase twists;
4. derive branch symmetry, amplitude selection, normalization, and response continuity
   from relational dynamics (given continuity, the extension from rational symmetric
   branches to arbitrary normalized amplitudes is now checked);
5. derive the now-checked Schwarzschild thermodynamic and evaporation formulas
   from microscopic quantum geometry, including greybody factors and information recovery;
6. derive the now-checked leading slow-roll spectra and consistency relation from
   microscopic relational dynamics and confront higher-order predictions with data;
7. derive the now-checked reversible clock-isomorphism hypotheses from realistic
   interacting quantum clocks with finite accuracy and backreaction.
