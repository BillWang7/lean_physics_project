import PhysicsProject.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Physics
noncomputable section

open scoped Interval RealInnerProductSpace

/--
Derivative of kinetic energy.

This lemma proves that d/dt KE(t) = ⟪m • acc x t, vel x t⟫.

From a physics perspective, this shows that the time derivative of KE is power (F · v).

lemma was proved with the help of Will Harris.
-/
lemma deriv_KE {m : ℝ} {x : Trajectory} (hv : Differentiable ℝ (vel x)):
    deriv (kineticEnergy m x) = fun t ↦ ⟪m • acc x t, vel x t⟫ := by
    unfold acc vel kineticEnergy

    -- norm squared of velocity is equal to inner product of velocity with itself
    have : (fun t ↦ 1 / 2 * m * ‖vel x t‖ ^ 2) = (fun t ↦ (1 / 2 * m * ⟪vel x t, vel x t⟫)) := by
        funext t
        rw [← real_inner_self_eq_norm_sq]
    rw [this]

    -- derivative is linear
    have : deriv (fun t ↦ 1 / 2 * m * ⟪vel x t, vel x t⟫) = fun t ↦ 1 / 2 * m * deriv (fun t ↦ ⟪vel x t, vel x t⟫) t := by
        simp
    rw [this]

    -- derivative of inner prouduct is <f, g'> + <f', g>
    have : deriv (fun t ↦ ⟪vel x t, vel x t⟫) =
        fun t ↦ (⟪vel x t, acc x t⟫ + ⟪acc x t, vel x t⟫) := by
      funext t
      -- get pointwise differentiability from hv
      have hf : DifferentiableAt ℝ (vel x) t := hv.differentiableAt
      have hg : DifferentiableAt ℝ (vel x) t := hv.differentiableAt
      -- use the lemma from Mathlib.Analysis.InnerProductSpace.Calculus
      simpa [acc] using deriv_inner_apply (𝕜 := ℝ) (f := vel x) (g := vel x) (x := t) hf hg
    rw [this]

    -- Inner product is symmetric
    funext t
    have hsymm : ⟪vel x t, acc x t⟫ = ⟪acc x t, vel x t⟫ := by
      simpa using real_inner_comm (acc x t) (vel x t)

    calc
        1 / 2 * m * (⟪vel x t, acc x t⟫ + ⟪acc x t, vel x t⟫)
        = 1 / 2 * m * (⟪acc x t, vel x t⟫ + ⟪acc x t, vel x t⟫) := by simp [hsymm]

      _ = 1 / 2 * m * 2 * ⟪acc x t, vel x t⟫ := by ring
      _ = m * ⟪acc x t, vel x t⟫ := by ring
      _ = ⟪m • acc x t, vel x t⟫ := by
        ring
        simp [inner_smul_left]


/--
Work–kinetic energy theorem in ℝ³.

Mathematically, this states that for a particle of mass 'm' moving along 'x'
and subject to a force 'F' satisfying Newton's law, the change in kinetic
energy from time 't₀' to time 't₁' is equal to the work done by `F.

From a physics perspectives, this states that work is accounted
for exactly as a change in kinetic energy. When the integral on the
right-hand side is zero (no net work done), then the change in KE energy also zero,
meaning energy is conserved.

This theorem was proved with the assistant of ChatGPT.
-/
theorem KE_work_thm {m : ℝ} {x : Trajectory}
    {F : ℝ → R3}
    (hv : Differentiable ℝ (vel x))
    (hN : NewtonsLaw m F x)
    (hF_cont : Continuous F)
    {t₀ t₁ : ℝ} :
    kineticEnergy m x t₁ - kineticEnergy m x t₀
      = work F x t₀ t₁ := by

    have hKE := deriv_KE (m := m) (x := x) hv
    have hKEF : deriv (kineticEnergy m x) = fun t ↦ ⟪F t, vel x t⟫ := by
        funext t
        have hpoint := congrArg (fun f => f t) hKE
    -- hpoint : deriv (kineticEnergy m x) t = ⟪m • acc x t, vel x t⟫
        have hNt : F t = m • acc x t := hN t
        simpa [hNt] using hpoint
    unfold work
      -- Differentiability of KE on the interval
    have hdiff_all : Differentiable ℝ (kineticEnergy m x) := by
    -- kineticEnergy m x t = (1/2 * m) * ‖vel x t‖^2
        unfold kineticEnergy
    -- hv : Differentiable ℝ (vel x)
        have hnorm : Differentiable ℝ (fun t ↦ ‖vel x t‖ ^ 2) :=
        (Differentiable.norm_sq (𝕜 := ℝ) (f := vel x) hv)
        have hscale : Differentiable ℝ (fun t ↦ (1 / 2 * m) * ‖vel x t‖ ^ 2) :=
        hnorm.const_mul (1 / 2 * m)
        simpa using hscale

    have hdiff :
    ∀ t ∈ Set.uIcc t₀ t₁,
      DifferentiableAt ℝ (kineticEnergy m x) t := by
        intro t ht
        exact hdiff_all.differentiableAt

  -- Continuity of f' = fun t ↦ ⟪F t, vel x t⟫ on the interval
    have hvel_cont : Continuous (vel x) := hv.continuous
  -- continuity of the inner product of two continuous maps
  -- continuity of the integrand t ↦ ⟪F t, vel x t⟫
    have hFprime_cont : Continuous fun t ↦ ⟪F t, vel x t⟫ := by
    -- uses the lemma `Continuous.inner`
        exact Continuous.inner hF_cont hvel_cont

  -- restrict to the closed interval
    have hcont :
        ContinuousOn (fun t ↦ ⟪F t, vel x t⟫) (Set.uIcc t₀ t₁) :=
            hFprime_cont.continuousOn

  -- apply FTC
    have hFTC :
      ∫ t in t₀..t₁, (fun t ↦ ⟪F t, vel x t⟫) t
        = kineticEnergy m x t₁ - kineticEnergy m x t₀ :=
    intervalIntegral.integral_deriv_eq_sub'
      (f := kineticEnergy m x)
      (f' := fun t ↦ ⟪F t, vel x t⟫)
      (a := t₀) (b := t₁)
      hKEF hdiff hcont

    rw [hFTC]


/--
Derivative of momentum for one particle.

This lemma proves that: d/dt (momentum m x t) = m • acc x t

From a physics perspective, this lemma states that the time derivative of momentum is m * a,
or force.

This lemma was proved with the assistant of ChatGPT.

-/
lemma deriv_momentum_eq_ma {m : ℝ} {x : Trajectory}
    (hv : Differentiable ℝ (vel x)) :
    deriv (momentum m x) = fun t ↦ m • acc x t := by

  unfold momentum acc vel
  funext t
  -- hv gives pointwise differentiability of vel
  have hvat : DifferentiableAt ℝ (vel x) t := hv.differentiableAt
  -- hasDerivAt for vel x, with derivative deriv (vel x) t
  have hHas : HasDerivAt (vel x) (deriv (vel x) t) t := hvat.hasDerivAt
  -- scale by m using HasDerivAt.const_smul
  have hHas' : HasDerivAt (fun s ↦ m • vel x s) (m • deriv (vel x) t) t :=
    hHas.const_smul m
  -- turn that into an equality on deriv
  have hDeriv := hHas'.deriv
  -- RHS is m • deriv (vel x) t, which is m • acc x t
  simpa using hDeriv


/--
Conservation of momentum for one free particle.

This theorem proves that for any t0 and t1,
momentum at t0 is always equal to momentum at t1 for a free particle
From a physics perspectives, if there is no net external force,
then momentum is constant in time.

This theorem was proved with the assistant of ChatGPT.
-/
theorem conserv_of_momentum_free_particle
    {m : ℝ} {x : Trajectory} {F : ℝ → R3}
    (hv : Differentiable ℝ (vel x))
    (hN : NewtonsLaw m F x)
    (hFzero : FreeParticle F)
    {t₀ t₁ : ℝ} :
    momentum m x t₁ = momentum m x t₀ := by

  -- derivative of momentum
  have hDerivMom := deriv_momentum_eq_ma (m := m) (x := x) hv

  -- Use Newton's law: F t = m • acc x t
  have hDeriv_eq_F : deriv (momentum m x) = F := by
    funext t
    have hpoint := congrArg (fun f => f t) hDerivMom
    -- hpoint : deriv (momentum m x) t = m • acc x t
    have hNt : F t = m • acc x t := hN t
    -- Rewrite RHS as F t
    simpa [hNt] using hpoint

  -- force is zero
  have hF_eq_zero : F = fun _ : ℝ => (0 : R3) := by
    funext t
    exact hFzero t

  -- So the derivative of momentum is zero
  have hDeriv_zero : deriv (momentum m x) = fun _ : ℝ => (0 : R3) := by
    simpa [hF_eq_zero] using hDeriv_eq_F

  -- apply FTC to get: ∫ deriv(momentum) = momentum(t₁) - momentum(t₀)

  -- build the hypotheses for FTC

  -- global differentiability of momentum
  have hdiff_all : Differentiable ℝ (momentum m x) := by
    -- from hv : Differentiable ℝ (vel x) and momentum = m • vel x
    simpa [momentum] using hv.const_smul m

  -- pointwise differentiability on the closed interval [[t₀, t₁]]
  have hdiff : ∀ t ∈ Set.uIcc t₀ t₁,
      DifferentiableAt ℝ (momentum m x) t := by
    intro t ht
    exact (hdiff_all t)

  -- continuity of f' (which is just the constant zero map)
  have hcont : ContinuousOn (fun _ : ℝ => (0 : R3)) (Set.uIcc t₀ t₁) := by
    -- constant function is continuous everywhere, hence continuous on uIcc
    simpa using
      (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => (0 : R3)) (Set.uIcc t₀ t₁))

  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub'
      (f := momentum m x)
      (f' := fun _ : ℝ => (0 : R3))
      (a := t₀) (b := t₁)
      hDeriv_zero
      hdiff
      hcont

  -- integral of zero is zero, so the difference of momenta is zero
  have hIntZero : ∫ t in t₀..t₁, (fun _ : ℝ => (0 : R3)) t = (0 : R3) := by
    simp

  -- From FTC: 0 = momentum t₁ - momentum t₀
  have hDiffZero : momentum m x t₁ - momentum m x t₀ = (0 : R3) := by
    -- first get 0 = momentum t₁ - momentum t₀
    have h : (0 : R3) = momentum m x t₁ - momentum m x t₀ := by
      simpa [hIntZero] using hFTC
    -- now flip the sides
    simpa [eq_comm] using h

  -- rearrange (a - b = 0) to get a = b
  have hEq := congrArg (fun v => v + momentum m x t₀) hDiffZero
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hEq


end
end Physics
