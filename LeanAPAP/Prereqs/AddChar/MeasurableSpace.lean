import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

namespace AddChar
variable {A M : Type*} [AddMonoid A] [Monoid M]

instance instMeasurableSpace : MeasurableSpace (AddChar A M) := ⊤
instance instDiscreteMeasurableSpace : DiscreteMeasurableSpace (AddChar A M) := ⟨fun _ ↦ trivial⟩

end AddChar
