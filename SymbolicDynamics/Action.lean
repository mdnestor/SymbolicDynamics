/-

some alternative definitions using monoid actions

-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Separation
import Mathlib.Topology.Connected.TotallyDisconnected


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

def local_map {T X Y Z: Type} [Monoid T] [MulAction T X] {S: Set T}
  (F: (X → Y) → X → Z) (μ: (S → Y) → Z): Prop :=
  ∀ u: X → Y, ∀ x: X, F u x = μ (fun t => u (t.val • x))

-- requires a commutative monoid.. can this be weakened?
theorem local_map_implies_equivariant {T X Y Z: Type} [CommMonoid T] [MulAction T X] {S: Set T}
  (F: (X → Y) → X → Z) (μ: (S → Y) → Z) (h: local_map F μ): equivariant T F := by
  intro u t
  ext x
  rw [h (fun x ↦ u (t • x)) x]
  rw [h u (t • x)]
  apply congrArg
  ext
  repeat rw [←mul_smul]
  rw [mul_comm]

def memory_set {T X Y Z: Type} [Monoid T] [MulAction T X]
  (F: (X → Y) → X → Z) (S: Set T): Prop :=
  ∃ μ : (S → Y) → Z, local_map F μ

def sliding_block {T X Y Z: Type} [Monoid T] [MulAction T X]
  (F: (X → Y) → X → Z): Prop :=
  ∃ S: Set T, ∃ μ : (S → Y) → Z, local_map F μ

def mulSetPoint [Monoid T] [MulAction T X] (S: Set T) (x: X): Set X :=
  Set.image (fun t => t • x) S

def eq_on_implies {T X Y Z: Type} [Monoid T] [MulAction T X]
  (F: (X → Y) → X → Z) (S: Set T): Prop :=
  ∀ x: X, ∀ u v: X → Y, Set.EqOn u v (mulSetPoint S x) → F u x = F v x
