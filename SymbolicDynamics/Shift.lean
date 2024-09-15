/-

Results about Subshifts

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
import SymbolicDynamics.Main

def shift {M A: Type} [Mul M] (g: M): (M → A) → (M → A) :=
  fun x => x ∘ leftMul g

theorem shift_preimage_cylinder_eq {G A: Type} [Mul G] (g g': G) (S: Set A):
  Set.preimage (shift g) (cylinder g' S) = cylinder (g * g') S := by
  rfl

theorem shift_continuous {M A: Type} [Mul M] (g: M) [TopologicalSpace A] [DiscreteTopology A]:
  Continuous (fun x: M → A => shift g x) := by
  sorry
  /-
  apply (continuous_iff_preimage_basic_open pi_generateFrom_cylinders (shift g)).mpr
  intro C hC
  obtain ⟨g, U, _, hC2⟩ := hC
  rw [hC2]
  rw [shift_preimage_cylinder_eq]
  apply cylinder_open
  apply isOpen_discrete
  -/

class Subshift {M A: Type} [Mul M] [TopologicalSpace A] (S: Set (M → A)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ g: M, shift g x ∈ S

export Subshift (closed shift_invariant)

@[simp]
def empty (A: Type): Set A := ∅

theorem Subshift_empty {M A: Type} [Mul M] [TopologicalSpace A]:
  Subshift (empty (M → A)) := by
  constructor <;> simp

theorem Subshift_univ {M A: Type} [Mul M] [TopologicalSpace A]:
  Subshift (Set.univ (α := M → A)) := by
  constructor <;> simp

-- artbirary intersections of Subshifts are Subshifts
theorem Subshift_sInter {M A: Type} [Mul M] [TopologicalSpace A]
  (Λs: Set (Set (M → A))) (h: ∀ Λ ∈ Λs, Subshift Λ): Subshift (Set.sInter Λs) := by
  constructor
  apply isClosed_sInter
  intro Λ hΛ
  exact (h Λ hΛ).1
  intro x hx g Λ hΛ
  exact (h Λ hΛ).2 x (hx Λ hΛ) g

theorem Subshift_iInter {M A: Type} [Mul M] [TopologicalSpace A]
  {I: Type} (Λ: I → (Set (M → A))) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iInter Λ) := by
  constructor
  apply isClosed_iInter
  intro i
  exact (h i).1
  intro x hx g Λ hΛ
  simp at hx
  obtain ⟨i, hi⟩ := hΛ
  rw [←hi]
  exact (h i).2 x (hx i) g

theorem Subshift_iUnion {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  {I: Type} [Finite I] (Λ: I → Set (M → A)) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iUnion Λ) := by
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

-- the preimage of a subshift under a sliding block code is a subshift

-- may hold when A is not necessarily finite
theorem Subshift_preimage {M A B: Type} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (M → A) → (M → B)) (h: sliding_block_code F) (Λ2: Set (M → B)) [Subshift Λ2]:
    Subshift (Set.preimage F Λ2) := by
  have ⟨hF1, hF2⟩ := (curtis_hedlund_lyndon F).mp h
  constructor
  apply IsClosed.preimage
  exact hF1
  exact closed
  intro x hx g
  simp [shift]
  rw [hF2]
  exact shift_invariant (F x) hx g

theorem Subshift_image {M A B: Type} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (M → A) → (M → B)) (h: sliding_block_code F) (Λ1: Set (M → A)) [Subshift Λ1]:
    Subshift (Set.image F Λ1) := by
  have ⟨hF1, hF2⟩ := (curtis_hedlund_lyndon F).mp h
  constructor
  sorry
  intro x hx g
  obtain ⟨y, hy1, hy2⟩ := hx
  simp
  exists shift g y
  constructor
  exact shift_invariant y hy1 g
  simp [shift]
  rw [hF2, hy2]


/-

def local_map {A B T: Type} [Mul T] {S: Set T} [TopologicalSpace A] [TopologicalSpace B]
  {Λ1: Set (T → A)} {Λ2: Set (T → B)} [Subshift Λ1] [Subshift Λ2]
  (F: Λ1 → Λ2) (f: (S → A) → B): Prop :=
  ∀ x: Λ1, ∀ t: T, (F x).val t = f (Set.restrict S (x ∘ (leftMul t)))

def memory_set {A B T: Type} [Mul T] [TopologicalSpace A] [TopologicalSpace B]
  {Λ1: Set (T → A)} {Λ2: Set (T → B)} [Subshift Λ1] [Subshift Λ2]
  (F: Λ1 → Λ2) (S: Set T): Prop :=
  ∃ f: (S → A) → B, local_map F f

-- definition of sliding block code: there exists a finite memory set
-- todo: generalize to shift spaces besides the full shit spaces
def sliding_block_code {T A B: Type} [TopologicalSpace A] [TopologicalSpace B] [Mul T] {Λ1: Set (T → A)} {Λ2: Set (T → B)} [Subshift Λ1] [Subshift Λ2]
  (F: Λ1 → Λ2): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S

def equivariant {T A B: Type} [TopologicalSpace A] [TopologicalSpace B] [Mul T] {Λ1: Set (T → A)} {Λ2: Set (T → B)} [Subshift Λ1] [Subshift Λ2]
  (F: Λ1 → Λ2): Prop :=
  ∀ u: Λ1, ∀ t: T, F ⟨u.val ∘ leftMul t, shift_invariant u.val u.prop t⟩ = (F u).val ∘ leftMul t

-/
