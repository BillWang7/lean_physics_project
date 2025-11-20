import MathLib

namespace Physics
noncomputable section

abbrev Position := ℝ → ℝ

def vel (x : Position) : ℝ → ℝ := fun t => deriv x t

def acc (x : Position) : ℝ → ℝ := fun t => deriv (vel x) t

def kineticEnergy (m : ℝ) (x : Position) : ℝ → ℝ :=
  fun t => (1/2) * m * (vel x t)^2

/-- define specific U later. For eaxmple, U = 1/2 kx^2, where k is sprint const-/
def potentialEnergy (U : ℝ → ℝ) (x : Position) : ℝ → ℝ :=
  fun t => U (x t)

def totalEnergy (m : ℝ) (U : ℝ → ℝ) (x : Position) : ℝ → ℝ :=
  fun t => kineticEnergy m x t + potentialEnergy U x t

/-- Newton's 2nd law -/
def NewtonsLaw (m : ℝ) (F : ℝ → ℝ) (x : Position) : Prop :=
  ∀ t, F t = m * acc x t

/-- Work done by F(t) from t0 to t1 -/
def work (F : ℝ → ℝ) (x : Position) (t₀ t₁ : ℝ) : ℝ :=
    sorry
/-- how to define an integral?-/

def momentum (m : ℝ) (x : Position) : ℝ → ℝ :=
  fun t => m * vel x t


end 
end Physics
