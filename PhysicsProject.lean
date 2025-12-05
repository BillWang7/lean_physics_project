import PhysicsProject.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Physics
noncomputable section

open scoped Interval RealInnerProductSpace


lemma deriv_KE {m : ℝ} {x : Trajectory} (hv : Differentiable ℝ (vel x)):
    deriv (kineticEnergy m x) = fun t ↦ ⟪m • acc x t, vel x t⟫ := by
    unfold acc vel kineticEnergy
    have : (fun t ↦ 1 / 2 * m * ‖vel x t‖ ^ 2) = (fun t ↦ (1 / 2 * m * ⟪vel x t, vel x t⟫)) := by
        funext t
        rw [← real_inner_self_eq_norm_sq]
    rw [this]
    have : deriv (fun t ↦ 1 / 2 * m * ⟪vel x t, vel x t⟫) = fun t ↦ 1 / 2 * m * deriv (fun t ↦ ⟪vel x t, vel x t⟫) t := by
        simp
    rw [this]
    have : deriv (fun t ↦ ⟪vel x t, vel x t⟫) =
        fun t ↦ (⟪vel x t, acc x t⟫ + ⟪acc x t, vel x t⟫) := by
      funext t
      -- get pointwise differentiability from hv
      have hf : DifferentiableAt ℝ (vel x) t := hv.differentiableAt
      have hg : DifferentiableAt ℝ (vel x) t := hv.differentiableAt
      -- use the lemma from Mathlib.Analysis.InnerProductSpace.Calculus
      simpa [acc] using deriv_inner_apply (𝕜 := ℝ) (f := vel x) (g := vel x) (x := t) hf hg
    rw [this]

    -- inner product space is symmetric
    funext t
    have hsymm : ⟪vel x t, acc x t⟫ = ⟪acc x t, vel x t⟫ := by
      simpa using real_inner_comm (acc x t) (vel x t)

    calc
      1 / 2 * m * (⟪vel x t, acc x t⟫ + ⟪acc x t, vel x t⟫)
          = 1 / 2 * m * (⟪acc x t, vel x t⟫ + ⟪acc x t, vel x t⟫) := by
            simp [hsymm]
      _ = m * ⟪acc x t, vel x t⟫ := by
            -- (1/2) * 2 = 1, then reassociate
            ring
      _ = ⟪m • acc x t, vel x t⟫ := by
            -- bring m inside the inner product on the left
            ring
            simp [inner_smul_left]



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
      -- 3a. Differentiability of KE on the interval
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

  -- 3b. Continuity of f' = fun t ↦ ⟪F t, vel x t⟫ on the interval
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

  -- 4. Apply the Fundamental Theorem of Calculus:
  --    ∫ f' = f(b) - f(a)
    have hFTC :
      ∫ t in t₀..t₁, (fun t ↦ ⟪F t, vel x t⟫) t
        = kineticEnergy m x t₁ - kineticEnergy m x t₀ :=
    intervalIntegral.integral_deriv_eq_sub'
      (f := kineticEnergy m x)
      (f' := fun t ↦ ⟪F t, vel x t⟫)
      (a := t₀) (b := t₁)
      hKEF hdiff hcont
    -- h has the shape: ∫ f' = f b - f a
    rw [hFTC]






/-- If the acceleration is zero for all time, then momentum is constant in time. -/
theorem conserv_of_momentum {m : ℝ} {x : Trajectory}
    (hm : 0 < m) (hx : Differentiable ℝ x)
    (hF : ∀ t, acc x t = 0) :
    ∀ t, deriv (momentum m x) t = 0 := by
    sorry

end
end Physics
