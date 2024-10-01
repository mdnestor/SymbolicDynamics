
--import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions

import SymbolicDynamics.Blocks
import SymbolicDynamics.ProdiscreteTopology

variable {A B C T : Type*}

open Topology

def shift [Mul T] (t: T): (T → A) → (T → A) :=
  fun x => x ∘ leftMul t

-- basic results about the shift map
theorem shift_comp [Semigroup T] {x: T → A} {t1 t2: T}: shift t1 (shift t2 x) = shift (t2 * t1) x := by
  ext
  simp [shift, leftMul, mul_assoc]

theorem shift_one {x: T → A} [MulOneClass T]: shift 1 x = x := by
  ext
  simp [shift, leftMul]

theorem shift_eq {x: T → A} {t: T} [MulOneClass T]: (shift t x) 1 = x t := by
  simp [shift, leftMul]

theorem shift_preimage_cylinder_eq [Mul T] (t1 t2: T) (S: Set A):
  Set.preimage (shift t1) (cylinder t2 S) = cylinder (t1 * t2) S := by
  rfl

-- the shift map is continuous in the prodiscrete topology
theorem shift_continuous [Mul T] (t: T) [TopologicalSpace A] [DiscreteTopology A]:
  Continuous[Pi.topologicalSpace, Pi.topologicalSpace] (fun x: T → A => shift t x) := by
  rw [pi_generateFrom_cylinders]
  apply continuous_generateFrom_iff.mpr
  intro _
  simp
  intro _ _ hV
  rw [hV, shift_preimage_cylinder_eq]
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  simp

-- definition of shift-equivariance
def shift_equivariant [Mul T] (f: (T → A) → T → B): Prop :=
  ∀ x: T → A, ∀ t: T, f (shift t x) = shift t (f x)

theorem shift_equivariant_id [Mul T]: shift_equivariant (@id (T → A)) := by
  intro _ _
  rfl

theorem shift_equivariant_comp [Mul T] (f: (T → A) → T → B) (g: (T → B) → T → C)
  (h1: shift_equivariant f) (h2: shift_equivariant g): shift_equivariant (g ∘ f) := by
  intro _ _
  rw [Function.comp_apply, h1, h2]
  rfl

theorem shift_one_equivariant [MulOneClass T] {F: (T → A) → T → B} {x: T → A} {t: T}
  (hf: shift_equivariant F): F x t = F (shift t x) 1 := by
  calc
    F x t = F x (t * 1) := by rw [mul_one]
        _ = ((F x) ∘ (leftMul t)) 1 := by rfl
        _ = (shift t (F x)) 1 := by rfl
  rw [hf]

-- definition of a shift-invariant subset
def shift_invariant_subset [Mul T] (S: Set (T → A)): Prop :=
  ∀ x ∈ S, ∀ t: T, shift t x ∈ S

-- the universe is shift invariant
theorem shift_invariant_univ [Mul T]: shift_invariant_subset (@Set.univ (T → A)) := by
  intro; simp

-- the empty set is shift invariant
theorem shift_invariant_empty [Mul T]: shift_invariant_subset (@∅: Set (T → A)) := by
  intro; simp

-- artbirary intersection of shift invariant sets is shift invariant
theorem shift_invariant_inter [Mul T] {ι : Sort u} {S : ι → Set (T → A)}
  (h : ∀ i, shift_invariant_subset (S i)) :
  shift_invariant_subset (⋂ i, S i) := by
  intro x hx t
  simp_all
  intro i
  exact h i x (hx i) t

-- artbirary union of shift invariant sets is shift invariant
theorem shift_invariant_union [Mul T] {ι : Sort u} {S : ι → Set (T → A)}
  (h : ∀ i, shift_invariant_subset (S i)) :
  shift_invariant_subset (⋃ i, S i) := by
  intro x hx t
  simp_all
  obtain ⟨i, hi⟩ := hx
  exists i
  exact h i x hi t

-- the image of a shift-invariant subset under a shift-equivariant map is shift-invariant
theorem shift_invariant_equivariant_image [Mul T] {S: Set (T → A)} (hS: shift_invariant_subset S)
  {F: (T → A) → (T → B)} (hF: shift_equivariant F): shift_invariant_subset (Set.image F S) := by
  intro _ hy t
  obtain ⟨x, hx⟩ := hy
  exists shift t x
  constructor
  apply hS
  exact hx.left
  rw [← hx.right]
  apply hF

class Subshift [Mul T] [TopologicalSpace A] (S: Set (T → A)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ g: T, shift g x ∈ S

export Subshift (closed shift_invariant)

theorem Subshift_empty [Mul T] [TopologicalSpace A]:Subshift (∅: Set (T → A)) := {
  closed := by simp
  shift_invariant := by simp
}

theorem Subshift_univ [Mul T] [TopologicalSpace A]: Subshift (@Set.univ (T → A)) := {
  closed := by simp
  shift_invariant := by simp
}

-- artbirary intersections of Subshifts are Subshifts
theorem Subshift_sInter [Mul T] [TopologicalSpace A]
  {Λs: Set (Set (T → A))} (h: ∀ Λ ∈ Λs, Subshift Λ): Subshift (Set.sInter Λs) := {
  closed := by
    apply isClosed_sInter
    exact fun Λ hΛ => (h Λ hΛ).1
  shift_invariant := fun x hx g Λ hΛ =>(h Λ hΛ).2 x (hx Λ hΛ) g
  }

-- intersection of two subshifts is a subshift
theorem Subshift_inter {M A: Type*} [Mul M] [TopologicalSpace A]
  (Λ1 Λ2: Set (M → A)) (h1: Subshift Λ1) (h2: Subshift Λ2): Subshift (Λ1 ∩ Λ2) := by
  let Λs: Set (Set (M → A)) := {Λ1, Λ2}
  have: Λ1 ∩ Λ2 = Set.sInter {Λ1, Λ2} := by simp
  rw [this]
  have: ∀ Λ ∈ Λs, Subshift Λ := by
    intro _ hΛ
    simp_all
    cases hΛ with
    | inl => simp_all
    | inr => simp_all
  exact Subshift_sInter this

/- Arbitrary indexed intersection of subshifts is subshift -/
theorem Subshift_iInter {M A: Type*} [Mul M] [TopologicalSpace A]
  {I: Type*} (Λ: I → (Set (M → A))) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iInter Λ) := by
  apply Subshift_sInter
  intro _ hΛi
  simp at hΛi
  obtain ⟨i, hi⟩ := hΛi
  rw [←hi]
  exact h i

theorem Subshift_iUnion {M A: Type*} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  {I: Type*} [Finite I] (Λ: I → Set (M → A)) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iUnion Λ) := by
  constructor
  apply isClosed_iUnion_of_finite
  intro i
  exact (h i).1
  intro x hx g
  simp_all
  obtain ⟨i, hxi⟩ := hx
  exists i
  exact (h i).shift_invariant x hxi g

-- 1.57
theorem Subshift_constant [Mul T] [TopologicalSpace A] [DiscreteTopology A]:
  Subshift {x: T → A | ∃ a: A, ∀ t: T, x t = a} := {
  closed := by
    -- why is the set of constant functions closed in the prodiscrete topology?
    sorry
  shift_invariant := by
    intro x hx t
    --simp at hx
    obtain ⟨a, ha⟩ := hx
    --simp
    exists a
    intro t'
    simp [shift]
    exact ha (leftMul t t')
}

-- the preimage of a subshift under a block code is a subshift
-- may hold when A is not necessarily finite

-- the orbit closure of a set of configurations
def orbit_closure [Mul T] [TopologicalSpace A] (S: Set (T → A)): Set (T → A) :=
  closure (Set.image2 shift Set.univ S)

-- the orbit closure is a subshift
theorem orbit_closure_subshift {T: Type u1} {A: Type u2} [Mul T] [TopologicalSpace A]
  (S Λ: Set (T → A)): Subshift (orbit_closure S) := {
  closed := by simp [orbit_closure]
  shift_invariant := by
    intro x hx g U hU
    simp_all
    apply hU.right
    sorry
}

-- the orbit closure is the smallest subshift containing the generating set
def orbit_closure_least_subshift {T: Type u1} {A: Type u2} [Mul T] [TopologicalSpace A]
  {S Λ: Set (T → A)} (h1: Subshift Λ) (h2: S ⊆ Λ): (orbit_closure S) ⊆ Λ := by
  rw [← IsClosed.closure_eq h1.closed]
  apply closure_mono
  intro _ hx
  simp at hx
  obtain ⟨t, y, hy⟩ := hx
  rw [←hy.right]
  apply shift_invariant
  exact h2 hy.left

-- Subshifts of finite types


def appears_anywhere [Mul X] (u: X → Y) (b: Block X Y): Prop :=
  ∃ x: X, appears (shift x u) b

def shift_from_forbidden_block [Mul X] (b: Block X Y): Set (X → Y) :=
  {u | ¬ appears_anywhere u b}

def shift_from_forbidden_blocks [Mul X] (F: Set (Block X Y)): Set (X → Y) :=
  {u | ∀ b ∈ F, ¬ appears_anywhere u b}

example [Mul X] (F: Set (Block X Y)):
  shift_from_forbidden_blocks F = Set.sInter (Set.image (fun b => shift_from_forbidden_block b) F) := by
  simp [shift_from_forbidden_block, shift_from_forbidden_blocks]
  ext
  simp_all

-- 1.47.a
theorem shift_from_forbidden_blocks_is_shift [Monoid X] [TopologicalSpace Y] (F: Set (Block X Y)):
  Subshift (shift_from_forbidden_blocks F) := {
  closed := by
    sorry
  shift_invariant := by
    intro u hu x b hb
    specialize hu b hb
    simp_all [appears_anywhere]
    intro x'
    simp_all [appears, shift, leftMul, Function.comp, leftMul]
    specialize hu (x * x')
    intro h
    apply hu
    rw [←h]
    simp [Set.EqOn]
    intro _ _
    rw [mul_assoc]
  }

-- definition of F(X)
def patterns_not_found_in
  (U: Set (X → Y)): Set (Block X Y) :=
  Set.compl (blocks_in_configs U)

-- 1.47.b
theorem defining_set_eq [Mul X] [TopologicalSpace Y] (U: Set (X → Y)) (h: Subshift U):
  U = shift_from_forbidden_blocks (patterns_not_found_in U) := by
  sorry

theorem defining_set_contained [Mul X] [TopologicalSpace Y]
  (U: Set (X → Y)) (h: Subshift U) (F: Set (Block X Y)) (hF: U = shift_from_forbidden_blocks F):
  F ⊆ patterns_not_found_in U := by
  sorry


-- TODO: 1.47.c

-- Let U ⊆ (X → Y)
-- Then U is said to have "finite type" if it is generated by a finite set of forbidden blocks
def Subshift_of_finite_type [Mul X] [TopologicalSpace Y] (U: Set (X → Y)): Prop :=
  ∃ F: Set (Block X Y), Finite F ∧ U = shift_from_forbidden_blocks F

-- TODO: 1.48.a

-- 1.48.b

-- 1.48.e
theorem subshift_of_finite_type_univ [Mul X] [TopologicalSpace Y]:
  Subshift_of_finite_type (@Set.univ (X → Y)) := by
  exists ∅
  constructor
  exact Set.finite_empty
  simp [shift_from_forbidden_blocks]

-- intersection of subshfits of finite type is a subshift with finite type
theorem subshift_of_finite_type_inter [Mul X] [TopologicalSpace Y]
  {Λ1 Λ2: Set (X → Y)} (h1: Subshift_of_finite_type Λ1) (h2: Subshift_of_finite_type Λ2):
  Subshift_of_finite_type (Λ1 ∩ Λ2) := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  exists F1 ∪ F2
  constructor
  exact @Finite.Set.finite_union _ F1 F2 hF1.left hF2.left
  rw [hF1.right, hF2.right]
  ext u
  constructor
  intro ⟨hu1, hu2⟩
  intro b
  intro h
  cases h
  case inl h_left =>
    exact hu1 b h_left
  case inr h_right =>
    exact hu2 b h_right
  intro h
  constructor
  · intro b hb
    exact h b (Or.inl hb)
  · intro b hb
    exact h b (Or.inr hb)

-- Given y: Y, consider the constant map u: _ => y.
-- Show the subshift X = {u} is a subshift of finite type.
theorem subshift_of_finite_type_singleton [Mul X] [TopologicalSpace Y]
  {y: Y}: Subshift_of_finite_type {fun _: X=> y} := by
  -- We'll use a block that covers all of X and maps to y
  sorry
