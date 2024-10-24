
--import Mathlib.Topology.Defs.Basic
--import Mathlib.Topology.Constructions

import SymbolicDynamics.ProdiscreteTopology

variable {A B C T : Type*}

open Topology

def shift [Mul T] (t: T): (T → A) → (T → A) :=
  fun x => x ∘ leftMul t

-- basic results about the shift map
theorem shift_comp [Semigroup T] {x: T → A} {t1 t2: T}: shift t1 (shift t2 x) = shift (t2 * t1) x := by
  ext
  simp [shift, leftMul]
  rw [mul_assoc]

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

theorem shift_invariant_sUnion [Mul T] {Λs : Set (Set (T → A))} (h : ∀ Λ ∈ Λs, shift_invariant_subset Λ) : shift_invariant_subset (Set.sUnion Λs) := by
  intro x hx t
  obtain ⟨i, hi⟩ := hx
  exists i
  constructor
  exact hi.left
  exact (h i hi.left) x hi.right t

theorem shift_invariant_sInter [Mul T] {Λs : Set (Set (T → A))} (h: ∀ Λ ∈ Λs, shift_invariant_subset Λ): shift_invariant_subset (Set.sInter Λs) :=
  fun x hx t Λ hΛ => h Λ hΛ x (by simp_all) t



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

class ShiftSpace [Mul T] [TopologicalSpace A] (S: Set (T → A)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ g: T, shift g x ∈ S

export ShiftSpace (closed shift_invariant)

theorem ShiftSpace_empty [Mul T] [TopologicalSpace A]: ShiftSpace (∅: Set (T → A)) := {
  closed := by simp
  shift_invariant := by simp
}

theorem ShiftSpace_univ [Mul T] [TopologicalSpace A]: ShiftSpace (@Set.univ (T → A)) := {
  closed := by simp
  shift_invariant := by simp
}

-- artbirary intersections of shift spaces are shift spaces
theorem ShiftSpace_sInter [Mul T] [TopologicalSpace A]
  {Λs: Set (Set (T → A))} (h: ∀ Λ ∈ Λs, ShiftSpace Λ): ShiftSpace (Set.sInter Λs) := {
  closed := by
    apply isClosed_sInter
    exact fun Λ hΛ => (h Λ hΛ).1
  shift_invariant := fun x hx g Λ hΛ =>(h Λ hΛ).2 x (hx Λ hΛ) g
  }

-- finite union of shift spaces is a shift space
theorem ShiftSpace_sUnion [Mul T] [TopologicalSpace A]
  {Λs: Set (Set (T → A))} [Finite Λs] (h: ∀ Λ ∈ Λs, ShiftSpace Λ): ShiftSpace (Set.sUnion Λs) := {
  closed := by
    apply isOpen_compl_iff.mp
    rw [Set.compl_sUnion]
    apply Set.Finite.isOpen_sInter
    apply Set.Finite.image
    assumption
    intro _ hU
    obtain ⟨V, hV⟩ := hU
    simp [←hV.right]
    exact (h V hV.left).closed
  shift_invariant := by
    intro x hx t
    obtain ⟨i, hxi⟩ := hx
    exists i
    constructor
    exact hxi.left
    exact (h i hxi.left).shift_invariant x hxi.right t
  }

-- intersection of two subshifts is a subshift
theorem ShiftSpace_inter {M A: Type*} [Mul M] [TopologicalSpace A] (Λ1 Λ2: Set (M → A)) (h1: ShiftSpace Λ1) (h2: ShiftSpace Λ2): ShiftSpace (Λ1 ∩ Λ2) := by
  let Λs: Set (Set (M → A)) := {Λ1, Λ2}
  have: Λ1 ∩ Λ2 = Set.sInter {Λ1, Λ2} := by simp
  rw [this]
  have: ∀ Λ ∈ Λs, ShiftSpace Λ := by
    intro _ hΛ
    simp_all
    cases hΛ with
    | inl => simp_all
    | inr => simp_all
  exact ShiftSpace_sInter this

/- Arbitrary indexed intersection of subshifts is subshift -/
theorem ShiftSpace_iInter {M A: Type*} [Mul M] [TopologicalSpace A]
  {I: Type*} (Λ: I → (Set (M → A))) (h: ∀ i: I, ShiftSpace (Λ i)): ShiftSpace (Set.iInter Λ) := by
  apply ShiftSpace_sInter
  intro _ hΛi
  simp at hΛi
  obtain ⟨i, hi⟩ := hΛi
  rw [←hi]
  exact h i

theorem ShiftSpace_iUnion {M A: Type*} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  {I: Type*} [Finite I] (Λ: I → Set (M → A)) (h: ∀ i: I, ShiftSpace (Λ i)): ShiftSpace (Set.iUnion Λ) := by
  apply ShiftSpace_sUnion
  intro Λ hΛ
  obtain ⟨i, hi⟩ := hΛ
  rw [←hi]
  exact h i

-- 1.57
theorem ShiftSpace_constant [Mul T] [TopologicalSpace A] [DiscreteTopology A]:
  ShiftSpace {x: T → A | ∃ a: A, ∀ t: T, x t = a} := {
  closed := by
    -- why is the set of constant functions closed in the prodiscrete topology?
    sorry
  shift_invariant := by
    intro x hx t
    obtain ⟨a, ha⟩ := hx
    exists a
    intro t'
    exact ha (leftMul t t')
}

-- the preimage of a subshift under a block code is a subshift
-- may hold when A is not necessarily finite

-- the orbit closure of a set of configurations
def orbit_closure [Mul T] [TopologicalSpace A] (S: Set (T → A)): Set (T → A) :=
  closure (Set.image2 shift Set.univ S)

-- the orbit closure is a subshift
theorem orbit_closure_subshift {T: Type u1} {A: Type u2} [Mul T] [TopologicalSpace A]
  (S Λ: Set (T → A)): ShiftSpace (orbit_closure S) := {
  closed := by simp [orbit_closure]
  shift_invariant := by
    intro x hx g U hU
    simp_all
    apply hU.right
    sorry
}

-- the orbit closure is the smallest subshift containing the generating set
def orbit_closure_least_subshift {T: Type u1} {A: Type u2} [Mul T] [TopologicalSpace A]
  {S Λ: Set (T → A)} (h1: ShiftSpace Λ) (h2: S ⊆ Λ): (orbit_closure S) ⊆ Λ := by
  rw [← IsClosed.closure_eq h1.closed]
  apply closure_mono
  intro _ hx
  simp at hx
  obtain ⟨t, y, hy⟩ := hx
  rw [←hy.right]
  apply shift_invariant
  exact h2 hy.left
