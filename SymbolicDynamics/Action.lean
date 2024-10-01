--import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
--import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.Constructions

import SymbolicDynamics.Defs

variable {T X Y : Type*}

-- Let σ: T × X → X be an action of T on X
-- A subset S is called σ-invariant if for all x ∈ S and t: T, σ(t, x) ∈ S
def invariant (σ: SMul T X) (S: Set X): Prop :=
  ∀ t: T, ∀ x: X, x ∈ S → t • x ∈ S

-- Arbitrary unions and intersections of invariant subsets are invariant
theorem invariant_iUnion {σ: SMul T X}
  {ι: Type*} {S: ι → Set X} (h: ∀ i: ι, invariant σ (S i)):
  invariant σ (Set.iUnion S) := by
    intro t x hx
    simp_all
    obtain ⟨i, hi⟩ := hx
    exists i
    exact h i t x hi

theorem invariant_iInter {σ: SMul T X}
  {ι: Type*} {S: ι → Set X} (h: ∀ i: ι, invariant σ (S i)):
  invariant σ (Set.iInter S) := by
    intro t x hx Si hSi
    simp_all
    obtain ⟨i, hi⟩ := hSi
    rw [← hi]
    exact h i t x (hx i)

-- the empty set and the universal set are invariant
theorem invariant_univ [SMul T X]:
  invariant σ Set.univ := by
  intro; simp

theorem invariant_empty [SMul T X]:
  invariant σ ∅ := by
  intro; simp

/- Let X be a topological space and let σ: T × X → X be an action of T on X. -/
/- A subset S ⊆ X is a closed invariant subspace if it is both closed and invariant wrt. the action of T. -/
class ClosedInvariantSubspace {X T: Type*} [TopologicalSpace X] (σ: SMul T X) (S: Set X): Prop where
  closed: IsClosed S
  invariant: invariant σ S

/- Arbitrary intersections of closed invariant subspaces are closed invariant subspaces -/
theorem ClosedInvariantSubspace_iInter {σ: SMul T X} [TopologicalSpace X]
  {ι: Type*} {Λ: ι → Set X} (h: ∀ i: ι, ClosedInvariantSubspace σ (Λ i)):
  ClosedInvariantSubspace σ (Set.iInter Λ) := {
  closed := by
    apply isClosed_sInter
    simp
    exact fun i => (h i).closed
  invariant := invariant_iInter (fun i => (h i).invariant)
}



def shift_action [SMul T X] (t: T): (X → Y) → (X → Y) :=
  fun (u: X → Y) (x: X) => u (t • x)

def setMul_action [SMul T X] (S: Set T) (x: X): Set X :=
  Set.image (fun s => s • x) S

theorem setMul_action_mem [SMul T X] {S: Set T} (s: S)
  (x: X): (s.val • x) ∈ (setMul_action S x) := by
  exists s.val
  constructor
  exact s.prop
  rfl

def local_map_from_action {S: Set T} (f: (S → Y) → Z) (X: Type*) [SMul T X]: (X → Y) → X → Z := by
  intro u x
  let σ: S → (setMul_action S x) := fun s => ⟨s.val • x, setMul_action_mem s x⟩
  let u' := Set.restrict (setMul_action S x) u
  let v := u' ∘ σ
  exact f v

def shift_action_equivariant (F: (X → Y) → X → Z) (T: Type*) [SMul T X]: Prop :=
  ∀ u: X → Y, ∀ t: T, F (shift_action t u) = shift_action t (F u)

-- if T is commutative then
-- every local map from a left action generates a shift action equivariant map
theorem local_map_from_action_equivariant [CommMonoid T] [MulAction T X] {S: Set T} {f: (S → Y) → Z}:
  shift_action_equivariant (local_map_from_action f X) T := by
  intro _ _
  ext
  simp [local_map_from_action]
  apply congrArg
  ext
  simp [shift_action, ←mul_smul, ←mul_smul, mul_comm]

class GeneralizedShiftSpace (σ: SMul T X) [TopologicalSpace Y] (S: Set (X → Y)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ t: T, shift_action t x ∈ S

theorem GeneralizedShiftSpace_empty (σ: SMul T X) [TopologicalSpace Y]: GeneralizedShiftSpace σ (∅: Set (X → Y)) := {
  closed := by simp
  shift_invariant := by simp
}

theorem GeneralizedShiftSpace_univ (σ: SMul T X) [Mul T] [TopologicalSpace Y]: GeneralizedShiftSpace σ (@Set.univ (X → Y)) := {
  closed := by simp
  shift_invariant := by simp
}

theorem GeneralizedShiftSpace_iInter {σ: SMul T X} [Mul T] [TopologicalSpace Y]
  {ι: Type*} {Λ: ι → Set (X → Y)} (h: ∀ i: ι, GeneralizedShiftSpace σ (Λ i)):
  GeneralizedShiftSpace σ (Set.iInter Λ) := {
  closed := by
    apply isClosed_sInter
    simp
    intro i
    exact (h i).closed
  shift_invariant := by
    intro u hu t S hS
    simp_all
    obtain ⟨i, hi⟩ := hS
    rw [← hi]
    exact (h i).shift_invariant u (hu i) t
}

theorem GeneralizedShiftSpace_iUnion_finite {σ: SMul T X} [Mul T] [TopologicalSpace Y]
  {ι: Type*} [Finite ι] (Λ: ι → Set (X → Y)) (h: ∀ i: ι, GeneralizedShiftSpace σ (Λ i)): GeneralizedShiftSpace σ (Set.iUnion Λ) := by
  constructor
  apply isClosed_iUnion_of_finite
  intro i
  exact (h i).1
  intro x hx g
  simp_all
  obtain ⟨i, hxi⟩ := hx
  exists i
  exact (h i).shift_invariant x hxi g



class Subshift [Mul T] [TopologicalSpace A] (S: Set (T → A)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ g: T, shift g x ∈ S

-- from a subshift get a generalized shift space
def GeneralizedShiftSpace_from_Subshift [Mul T] [TopologicalSpace A] {S: Set (T → A)} (h: Subshift S):
  GeneralizedShiftSpace (SMul.mk fun t t': T => t * t') S := {
  closed := h.closed
  shift_invariant := h.shift_invariant
}

def Subshift_from_GeneralizedShiftSpace [Mul T] [TopologicalSpace A] {S: Set (T → A)} (h: GeneralizedShiftSpace (SMul.mk fun t t': T => t * t') S):
  Subshift S := {
  closed := h.closed
  shift_invariant := h.shift_invariant
}

theorem Subshift_iInter [Mul T] [TopologicalSpace A]
  {I: Type*} (Λ: I → (Set (T → A))) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iInter Λ) := by
  apply Subshift_from_GeneralizedShiftSpace
  exact GeneralizedShiftSpace_iInter (fun i => GeneralizedShiftSpace_from_Subshift (h i))

instance [SMul T X]: SMul T (X → Y) := SMul.mk shift_action
