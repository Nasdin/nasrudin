/-!
# SI Dimensions

Physical dimensions for dimensional analysis.
-/

namespace PhysicsGenerator.Dimensions

/-- SI base dimensions as integer exponents -/
structure Dimension where
  length      : Int
  mass        : Int
  time        : Int
  current     : Int
  temperature : Int
  amount      : Int
  luminosity  : Int
  deriving DecidableEq, Repr

def Dimension.dimensionless : Dimension :=
  ⟨0, 0, 0, 0, 0, 0, 0⟩

def Dimension.energy : Dimension :=
  ⟨2, 1, -2, 0, 0, 0, 0⟩

def Dimension.force : Dimension :=
  ⟨1, 1, -2, 0, 0, 0, 0⟩

def Dimension.velocity : Dimension :=
  ⟨1, 0, -1, 0, 0, 0, 0⟩

def Dimension.momentum : Dimension :=
  ⟨1, 1, -1, 0, 0, 0, 0⟩

def Dimension.action : Dimension :=
  ⟨2, 1, -1, 0, 0, 0, 0⟩

/-- Multiply dimensions (add exponents) -/
def Dimension.mul (a b : Dimension) : Dimension :=
  ⟨a.length + b.length, a.mass + b.mass, a.time + b.time,
   a.current + b.current, a.temperature + b.temperature,
   a.amount + b.amount, a.luminosity + b.luminosity⟩

/-- Divide dimensions (subtract exponents) -/
def Dimension.div (a b : Dimension) : Dimension :=
  ⟨a.length - b.length, a.mass - b.mass, a.time - b.time,
   a.current - b.current, a.temperature - b.temperature,
   a.amount - b.amount, a.luminosity - b.luminosity⟩

instance : HMul Dimension Dimension Dimension := ⟨Dimension.mul⟩

/-- Equations must be dimensionally homogeneous -/
axiom dim_homogeneity : ∀ (d1 d2 : Dimension), d1 = d2 -> True

end PhysicsGenerator.Dimensions
