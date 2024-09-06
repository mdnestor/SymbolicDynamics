/-

Results about subshifts

-/

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

import SymbolicDynamics.ProdiscreteTopology


def shift {M A: Type} [Mul M] (g: M): (M → A) → (M → A) :=
  fun x => x ∘ leftMul g

-- let V be open set
-- then V = ∪ ∩ C
-- want to show preimage of V is open
-- σ ^(-1) (V) = σ ^(-1) ∪ ∩ C = ∪ ∩ σ ^(-1) C
-- so it suffices to show the preimage of every cylinder is open

-- cylinder is {x: G → A | x g  ∈ S}
-- i think the preimage by shift is another cylinder lol

theorem shift_preimage_cylinder_eq {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  (g g': M) (S: Set A):  Set.preimage (shift g) (cylinder g' S) = cylinder (g * g') S := by
  rfl

theorem shift_preimage_cylinder_open {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  (g g': M) (S: Set A):  IsOpen (Set.preimage (shift g) (cylinder g' S)) := by
  rw [shift_preimage_cylinder_eq]
  apply cylinder_open
  simp

theorem shift_continuous {M A: Type} [Mul M] (g: M) [TopologicalSpace A] [DiscreteTopology A]:
  Continuous (fun x: M → A => x ∘ leftMul g) := by
  constructor
  intro V hV
  have hV2 := union_of_finite_intersection_of_cylinders_of_open hV
  simp [union_of_finite_inter_of_cylinders, finite_intersection_of_cylinders] at hV2
  obtain ⟨ UU, hUU⟩ := hV2
  rw [← hUU.1]
  simp
  apply isOpen_sUnion
  intro U
  simp
  intro x hx
  rw [← hx]
  apply isOpen_sUnion
  intro U2 hU2
  simp at hU2
  rw [← hU2.2]
  obtain ⟨ I, hI1, hI2 ⟩ := hUU.2 x hU2.1
  obtain ⟨ g, a, hag⟩ := hI2
  rw [hag]
  rw [Set.preimage_iInter]
  apply isOpen_iInter_of_finite
  intro i
  apply shift_preimage_cylinder_open

def subshift {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A] (S: Set (M → A)): Prop :=
  IsClosed S ∧ ∀ x ∈ S, ∀ g: M, shift g x ∈ S

@[simp]
def empty (A: Type): Set A := ∅

theorem subshift_empty {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]:
  subshift (empty (M → A)) := by
  constructor <;> aesop

theorem subshift_univ {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]:
  subshift (Set.univ (α := M → A)) := by
  constructor <;> aesop

-- artbirary intersections of subshifts are subshifts
theorem subshift_sInter {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  (Λs: Set (Set (M → A))) (h: ∀ Λ ∈ Λs, subshift Λ): subshift (Set.sInter Λs) := by
  constructor
  apply isClosed_sInter
  intro Λ hΛ
  exact (h Λ hΛ).1
  intro x hx g Λ hΛ
  exact (h Λ hΛ).2 x (hx Λ hΛ) g

theorem subshift_iInter {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  {I: Type} (Λ: I → (Set (M → A))) (h: ∀ i: I, subshift (Λ i)): subshift (Set.iInter Λ) := by
  constructor
  apply isClosed_iInter
  intro i
  exact (h i).1
  intro x hx g Λ hΛ
  simp at hx
  obtain ⟨i, hi⟩ := hΛ
  rw [←hi]
  exact (h i).2 x (hx i) g

theorem subshift_iUnion {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  {I: Type} [Finite I] (Λ: I → Set (M → A)) (h: ∀ i: I, subshift (Λ i)): subshift (Set.iUnion Λ) := by
  constructor
  apply isClosed_iUnion_of_finite
  intro i
  exact (h i).1
  intro x hx g
  let ⟨Λi, hΛi⟩ := hx
  exists Λi
  constructor
  exact hΛi.1
  simp at hx
  obtain ⟨i, hi⟩ := hx
  sorry
