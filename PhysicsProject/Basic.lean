import MathLib.Tactic

namespace Physics
noncomputable section

open scoped RealInnerProductSpace Interval

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The trajectory of a particle in ℝ3 given time t ∈ ℝ-/
abbrev Trajectory := ℝ → R3

def vel (x : Trajectory) : ℝ → R3 := fun t => deriv x t

def acc (x : Trajectory) : ℝ → R3 := fun t => deriv (vel x) t

/-- Kinetic energy of a particle of mass `m` moving along `x` in ℝ³. -/
def kineticEnergy (m : ℝ) (x : Trajectory) : ℝ → ℝ :=
  fun t => (1/2) * m * ‖vel x t‖^2

/-- define specific U later. For eaxmple, U = 1/2 kx^2, where k is sprint const-/
def potentialEnergy (U : R3 → ℝ) (x : Trajectory) : ℝ → ℝ :=
  fun t => U (x t)

def totalEnergy (m : ℝ) (U : R3 → ℝ) (x : Trajectory) : ℝ → ℝ :=
  fun t => kineticEnergy m x t + potentialEnergy U x t

/-- Newton's 2nd law -/
def NewtonsLaw (m : ℝ) (F : ℝ → R3) (x : Trajectory) : Prop :=
  ∀ t, F t = m • acc x t

/-- Work done by F(t) from t0 to t1 -/
def work (F : ℝ → R3) (x : Trajectory) (t₀ t₁ : ℝ) : ℝ :=
  ∫ t in t₀..t₁, ⟪F t, vel x t⟫

/-- Linear momentum of a particle of mass `m` moving along `x` in ℝ³. -/
def momentum (m : ℝ) (x : Trajectory) : ℝ → R3 :=
  fun t => m • vel x t


end
end Physics
