import Mathlib.Tactic

namespace Physics
noncomputable section

open scoped RealInnerProductSpace Interval

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Define the trajectory of a particle in ℝ3 given time t ∈ ℝ-/
abbrev Trajectory := ℝ → R3

/-- Define the velocity function of a particle in R3 given trajectory function-/
def vel (x : Trajectory) : ℝ → R3 := fun t => deriv x t

/-- Define the acceleration function of a particle in R3 given trajectory function-/
def acc (x : Trajectory) : ℝ → R3 := fun t => deriv (vel x) t

/-- Define kinetic energy of a particle of mass 'm' moving along 'x' in R3. -/
def kineticEnergy (m : ℝ) (x : Trajectory) : ℝ → ℝ :=
  fun t => (1/2) * m * ‖vel x t‖^2

/-- Define Newton's 2nd law -/
def NewtonsLaw (m : ℝ) (F : ℝ → R3) (x : Trajectory) : Prop :=
  ∀ t, F t = m • acc x t

/-- A particle is "free" if the net external force is zero at all times -/
def FreeParticle (F : ℝ → R3) : Prop :=
  ∀ t : ℝ, F t = 0

/-- Define work done by F(t) from t0 to t1 on a particle moving along 'x' in R3 -/
def work (F : ℝ → R3) (x : Trajectory) (t₀ t₁ : ℝ) : ℝ :=
  ∫ t in t₀..t₁, ⟪F t, vel x t⟫

/-- Linear momentum of a particle of mass 'm' moving along 'x' in ℝ³. -/
def momentum (m : ℝ) (x : Trajectory) : ℝ → R3 :=
  fun t => m • vel x t

end
end Physics
