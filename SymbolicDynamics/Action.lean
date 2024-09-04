
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs

def equivariant {X Y Z: Type} (T: Type) [Monoid T] [MulAction T X]
  (F: (X → Y) → X → Z): Prop :=
  ∀ u: X → Y, ∀ t: T, F (fun x => u (t • x)) = fun x => (F u) (t • x)

def equivariant_compose {T X Y Z W: Type} [Monoid T] [MulAction T X]
  {F: (X → Y) → X → Z} {G: (X → Z) → X → W}
  (h1: equivariant T F) (h2: equivariant T G):
  equivariant T (G ∘ F) := by
  simp [equivariant]
  intros
  rw [h1, h2]
