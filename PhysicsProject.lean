import PhysicsProject.Basic

namespace Physics

lemma deriv_KE {m : ℝ} {x : Position} (hm : 0 < m) (hx : Differentiable ℝ x) :
    (∀ t, deriv (kineticEnergy m x) t = (m * acc x t) * (vel x t)) := by
    sorry

theorem KE_work_thm {m : ℝ} {x : Position} {F : ℝ → ℝ} (hm : 0 < m)
    (hx : Differentiable ℝ x)
    (hN : ∀ t, F t = m * acc x t) {t₀ t₁ : ℝ} : kineticEnergy m x t₁ - kineticEnergy m x t₀
      = work F x t₀ t₁ := by
      sorry

theorem conserv_of_energy {m : ℝ} {U : ℝ → ℝ} {x : Position} (hx : Differentiable ℝ x) (hU : Differentiable ℝ U)
    (h_force : ∀ t, -(deriv U (x t)) * vel x t = (m * acc x t) * vel x t) :
    ∀ t, deriv (totalEnergy m U x) t = 0 := by
    sorry

theorem conserv_of_momentum {m : ℝ} {x : Position} (hm : 0 < m) (hx : Differentiable ℝ x)
    (hF : ∀ t, acc x t = 0) :
    ∀ t, deriv (momentum m x) t = 0 := by
    sorry

end Physics
