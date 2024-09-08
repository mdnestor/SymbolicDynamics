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

theorem shift_preimage_cylinder_eq {G A: Type} [Mul G] (g g': G) (S: Set A):
  Set.preimage (shift g) (cylinder g' S) = cylinder (g * g') S := by
  rfl

theorem shift_continuous {M A: Type} [Mul M] (g: M) [TopologicalSpace A] [DiscreteTopology A]:
  Continuous (fun x: M → A => shift g x) := by
  apply (continuous_iff_preimage_basic_open prodiscrete_generateFrom_cylinders (shift g)).mpr
  intro C hC
  obtain ⟨g, U, hC⟩ := hC
  rw [hC]
  rw [shift_preimage_cylinder_eq]
  apply cylinder_open
  apply isOpen_discrete

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
