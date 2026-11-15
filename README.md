# Formal Verification of Classical Mechanics in Lean 4

Machine-checked proofs of two basic results from Newtonian mechanics, written in [Lean 4](https://lean-lang.org/) on top
of [Mathlib](https://github.com/leanprover-community/mathlib4):

1. **The work–energy theorem**: the change in a particle's kinetic energy equals the work done on it.
2. **Conservation of momentum for a free particle**: with no net force, momentum never changes.

Lean checks every step, so the theorems hold exactly as stated, under exactly the stated assumptions. Course project
for Duke MATH 248S (Fall 2025).

## The model

A particle moves through 3D space, ℝ³ (Mathlib's `EuclideanSpace ℝ (Fin 3)`). Everything is defined from its
trajectory `x : ℝ → ℝ³` (position at time `t`) in [`PhysicsProject/Basic.lean`](PhysicsProject/Basic.lean):

| Definition | Meaning | In Lean |
|---|---|---|
| `vel x` | velocity, v = dx/dt | `deriv x` |
| `acc x` | acceleration, a = dv/dt | `deriv (vel x)` |
| `kineticEnergy m x` | KE = ½ m ‖v‖² | `fun t => (1/2) * m * ‖vel x t‖^2` |
| `momentum m x` | p = m v | `fun t => m • vel x t` |
| `work F x t₀ t₁` | W = ∫ F · v dt from t₀ to t₁ | `∫ t in t₀..t₁, ⟪F t, vel x t⟫` |
| `NewtonsLaw m F x` | F = m a at every time | `∀ t, F t = m • acc x t` |
| `FreeParticle F` | no net force | `∀ t, F t = 0` |

## The results

All in [`PhysicsProject.lean`](PhysicsProject.lean).

| Name | Statement | Physical meaning |
|---|---|---|
| `deriv_KE` | d(KE)/dt = ⟨m a, v⟩ | the rate of change of kinetic energy is power (F · v) |
| `KE_work_thm` | KE(t₁) − KE(t₀) = W(t₀, t₁) | **work–energy theorem** |
| `deriv_momentum_eq_ma` | dp/dt = m a | the rate of change of momentum is force |
| `conserv_of_momentum_free_particle` | p(t₁) = p(t₀) | **momentum is conserved when no force acts** |

The assumptions are explicit hypotheses. The velocity must be differentiable, the force must obey Newton's second
law, and for the work–energy theorem the force must be continuous so that the integral is well behaved.

### How the proofs work

- **`deriv_KE`**: rewrite ‖v‖² as the inner product ⟨v, v⟩, differentiate it with the product rule
  (⟨v, a⟩ + ⟨a, v⟩), and use symmetry of the inner product to get m⟨a, v⟩.
- **`KE_work_thm`**: Newton's law turns d(KE)/dt into ⟨F, v⟩. Kinetic energy is differentiable and ⟨F, v⟩ is
  continuous, so the fundamental theorem of calculus (`intervalIntegral.integral_deriv_eq_sub'`) gives
  ∫ ⟨F, v⟩ dt = KE(t₁) − KE(t₀).
- **`conserv_of_momentum_free_particle`**: dp/dt = m a = F = 0, so by the fundamental theorem of calculus
  p(t₁) − p(t₀) = ∫ 0 dt = 0.

## Building

Needs [elan](https://github.com/leanprover/elan) (the Lean version manager). The Lean version is pinned in
`lean-toolchain` and the Mathlib version in `lake-manifest.json`.

```bash
lake exe cache get   # download prebuilt Mathlib (much faster than compiling it)
lake build
```

A successful build means every proof checks; the project contains no `sorry` (unproved steps). GitHub Actions runs
the same build on every push.

## Credits

`deriv_KE` was proved with help from Will Harris. ChatGPT assisted with parts of `KE_work_thm`,
`deriv_momentum_eq_ma` and `conserv_of_momentum_free_particle`, as noted in each docstring.
