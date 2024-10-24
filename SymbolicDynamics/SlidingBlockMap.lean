/-

Main reults:

-- defines the shift map and proves it is continuous
-- defines sliding block code
-- proves the Curtis–Hedlund–Lyndon (CHL) theorem
-- defines subshifts

Notation
-- A, B, C for alphabets, T for tape positions equipped with some algebraic structure
-- results are general as possible, some use `MulOneClass` aka unital magma
-- x, y, z: T → A for tape configurations

TODO:

-- prove CHL theorem from the uniform variant (likely simpler proof)
-- variant of CHL theorem for subshifts
-- characterize subshifts in terms of forbidden blocks
-- shifts of finite type
-- sofic shifts
-- some refactoring? instead of state a local map/memory set exists, simply provide evidence

References:

-- "Cellular automata and groups" by Ceccherini-Silberstein and Coornaert (2010)
-- "A note on the definition of sliding block codes and the Curtis-Hedlund-Lyndon Theorem" by Sobottka and Goçcalves (2017) https://arxiv.org/abs/1507.02180
-- "Some notes on the classification of shift spaces: Shifts of Finite Type; Sofic Shifts; and Finitely Defined Shifts" by Sobottka (2020) https://arxiv.org/abs/2010.10595
-- "Symbolic dynamics" on Scholarpedia http://www.scholarpedia.org/article/Symbolic_dynamics

-/

import Mathlib.Topology.Algebra.MulAction

import SymbolicDynamics.ShiftSpace

open Topology

variable {A B C T : Type*}

-- main definitions:
-- sliding block map, local map, and memory set
def local_map [Mul T] {S: Set T} (F: (T → A) → T → B) (f: (S → A) → B): Prop :=
  ∀ (x: T → A) (t: T), F x t = f (Set.restrict S (shift t x))

def sliding_block_from [Mul T] {S: Set T} (f: (S → A) → B): (T → A) → T → B :=
  fun (x: T → A) (t: T) => f (Set.restrict S (shift t x))

def is_sliding_block_from [Mul T] {S: Set T} (F: (T → A) → T → B) (f: (S → A) → B): Prop :=
  F = sliding_block_from f

def has_local_map [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ (S: Set T) (f: (S → A) → B), F = sliding_block_from f

def has_finite_local_map [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ (S: Set T) (f: (S → A) → B), Finite S ∧ F = sliding_block_from f

def is_memory_set [Mul T] (F: (T → A) → T → B) (S: Set T): Prop :=
  ∃ (f: (S → A) → B), F = sliding_block_from f

-- if F has a local map then it is shiftu (t • s • x) = u (s • t • x)-equivariant
theorem local_map_equivariant [Semigroup T] {S: Set T} {F: (T → A) → T → B} {f: (S → A) → B}
  (h: local_map F f): shift_equivariant F := by
  intro u t
  ext t'
  rw [h (shift t u) t']
  repeat simp [shift]
  rw [h]
  congr
  rw [Set.restrict_eq_restrict_iff]
  apply Set.EqOn.mono (Set.subset_univ S)
  apply (Set.eqOn_univ ((u ∘ leftMul t) ∘ leftMul t') (shift (leftMul t t') u)).mpr
  ext
  simp [shift, leftMul]
  rw [mul_assoc]

-- if F is equivariant and T is a unital magma then the universe is a memory set

theorem local_map_univ [MulOneClass T] {F: (T → A) → T → B} (hf: shift_equivariant F):
  F = sliding_block_from (fun x: (@Set.univ T → A) => F (x ∘ (@Equiv.Set.univ T).invFun) 1) := by
  ext x t
  simp [sliding_block_from, shift]
  sorry

theorem local_map_id [MulOneClass T]:
  id = sliding_block_from (fun x: ({1}: Set T) → A => x ⟨1, rfl⟩) := by
  ext
  simp [id, sliding_block_from, shift, leftMul]

theorem memory_set_id [MulOneClass T]: is_memory_set (@id (T → A)) {1} := by
  exists fun x => x ⟨1, rfl⟩
  exact local_map_id


def restrict_further {X Y: Type*} {S1 S2: Set X} (h: S1 ⊆ S2) (f: S2 → Y): S1 → Y :=
  f ∘ Set.inclusion h

-- If there is a local map f: (S → A) → B and S ⊆ S'
-- there is a local map f': (S' → A) → B
-- such that SB(f) = SB(f')
theorem local_map_upward [Mul T]
  (S S': Set T) (f: (S → A) → B) (h: S ⊆ S'):
  sliding_block_from f = sliding_block_from fun x => f (x ∘ Set.inclusion h) := by
  rfl

-- If S is a memory set of F and S ⊆ S' then so is S'
theorem memory_set_upward [Mul T]
  (S S': Set T) (F: (T → A) → T → B) (h1: is_memory_set F S) (h2: S ⊆ S'): is_memory_set F S' := by
  obtain ⟨f, _⟩ := h1
  exists fun x => f (x ∘ Set.inclusion h2)

def setMul [Mul T] (S1 S2: Set T): Set T :=
  (Set.image2 fun t1 t2 => t1 * t2) S1 S2

-- Let f be a local map with memory set S
-- Suppose u and v are equal on Ω * S (pointwise multiplication)
-- Let F = SB(f) be the sliding block map from f
-- then F(u) and F(v) are equal on Ω
theorem local_map_eq [Mul T] {S Ω: Set T} {x y: T → A} (f: (S → A) → B) (h: Set.EqOn x y (setMul Ω S)): Set.EqOn (sliding_block_from f x) (sliding_block_from f y) Ω := by
  intro t hg
  rw [sliding_block_from]
  apply congrArg
  simp [Set.EqOn]
  intro t' _
  apply h
  exists t
  constructor
  . assumption
  . exists t'

-- Suppose F has a memory set S
-- Suppose u and v are equal on Ω * S (pointwise multiplication)
-- then F(u) and F(v) are equal on Ω
theorem memory_set_eq [Mul T] {S Ω: Set T} {x y: T → A} (F: (T → A) → T → B) (h1: Set.EqOn x y (setMul Ω S)) (h2: is_memory_set F S): Set.EqOn (F x) (F y) Ω := by
  obtain ⟨f, hf⟩ := h2
  rw [hf]
  exact local_map_eq f h1

-- definition of sliding block code: there exists a finite memory set
/-
def sliding_block_code [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S
-/

def is_sliding_block_map [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ S: Set T, ∃ f: (S → A) → B, Finite S ∧ F = sliding_block_from f

-- sliding block codes are shift-equivariant

theorem sliding_block_map_equivariant [Semigroup T] {S: Set T} (f: (S → A) → B): shift_equivariant (sliding_block_from f) := by
  intro u t
  ext t'
  simp [sliding_block_from, shift]
  congr
  rw [Set.restrict_eq_restrict_iff]
  apply Set.EqOn.mono (Set.subset_univ S)
  apply (Set.eqOn_univ ((u ∘ leftMul t) ∘ leftMul t') (shift (leftMul t t') u)).mpr
  ext
  simp [shift, leftMul, mul_assoc]



-- the shift map is a sliding sliding block code
-- TODO: weaken commutativity assumption?
theorem shift_is_sliding_block_code [CommMonoid T] (t: T): (fun x: T → A => shift t x) = sliding_block_from (fun x => x ⟨t, Set.mem_singleton t⟩) := by
  ext x t
  simp [sliding_block_from, shift, leftMul]
  rw [mul_comm]

theorem local_map_iff [Monoid T] (F: (T → A) → T → B) {S: Set T} (f: (S → A) → B): F = sliding_block_from f ↔ shift_equivariant F ∧ ∀ u, F u 1 = f (S.restrict u) := by
  constructor
  . intro h
    constructor
    . rw [h]
      exact sliding_block_map_equivariant f
    . intro x
      rw [h, sliding_block_from, shift_one]
  . intro h
    ext x t
    simp [sliding_block_from]
    rw [←h.right (shift t x), h.left]
    simp [shift, leftMul]

/- Gives the composition of two sliding blocks -/
theorem local_map_compose [Semigroup T] {S1 S2: Set T}
  {f1: (S1 → A) → B} {f2: (S2 → B) → C}:
  sliding_block_from f2 ∘ sliding_block_from f1 = sliding_block_from fun x: setMul S2 S1 → A => f2 (fun s2 => f1 (fun s1 => x ⟨s2.val * s1.val, ⟨s2.val, s2.prop, by exists s1.val; simp⟩⟩)) := by
  ext
  simp [sliding_block_from]
  congr
  ext
  simp [sliding_block_from, shift, Function.comp, leftMul, mul_assoc]
  rfl

theorem sliding_block_code_continuous [MulOneClass T] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] {S: Set T} (f: (S → A) → B) (h: Finite S): Continuous (sliding_block_from f) := by
  apply continuous_of_neighborhood_continuous.mpr
  intro x _ hV
  obtain ⟨Ω, hΩ⟩ := exists_finite_eqOn_nhd hV
  let ΩS := setMul Ω S
  exists eqOn_nhd x ΩS
  constructor
  . apply eqOn_nhd_is_nhd x
    apply Set.Finite.image2
    exact hΩ.left
    exact h
  . let F := sliding_block_from f
    have: Set.image F (eqOn_nhd x ΩS) ⊆ eqOn_nhd (F x) Ω := by
      intro Fy hFy
      simp [eqOn_nhd] at hFy
      obtain ⟨_, hy⟩ := hFy
      simp [eqOn_nhd, ←hy.right]
      apply local_map_eq
      exact hy.left
    exact le_trans this hΩ.right

-- helper lemmas
theorem exists_neighbor_eqAt_one [MulOneClass T] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] {F: (T → A) → T → B} (h: Continuous F):
  ∀ x, ∃ Ω: Set T, Finite Ω ∧ ∀ y, y ∈ eqOn_nhd x Ω → F x 1 = F y 1 := by
    let φ := proj 1 ∘ F
    have hφ : Continuous φ := Continuous.comp (continuous_apply 1) h
    intro x
    obtain ⟨V, hV⟩ := continuous_of_neighborhood_continuous.mp hφ x {φ x} (by simp)
    have h4 := (eqOn_nhd_forms_neighborhood_base x).right
    specialize h4 V hV.left
    obtain ⟨U, hU⟩ := h4
    simp_all
    obtain ⟨Ω, hΩ⟩ := hU.left
    exists Ω
    constructor
    exact hΩ.left
    intro y hy
    rw [← hΩ.right] at hy
    calc
      F x 1 = φ x := by rfl
          _ = φ y := by rw [Eq.symm ((hV.right y) (hU.right hy))]
          _ = F y 1 := by rfl

theorem exists_extension {X Y: Type*} {S: Set X} [Nonempty Y]:
  ∀ f: S → Y, ∃ F: X → Y, Set.restrict S F = f := by
  classical -- ensures decidable membership of S
  intro f
  exists fun x => if h: x ∈ S then f ⟨x, h⟩ else Classical.ofNonempty
  simp


@[simp]
def extension_constructive {X Y: Type*} [Nonempty Y] {S: Set X} [∀ x, Decidable (x ∈ S)] (f: S → Y) (y0: Y): X → Y :=
  fun x => if h: x ∈ S then f ⟨x, h⟩ else y0

@[simp]
noncomputable def extension_nonconstructive {X Y: Type*} [Nonempty Y] {S: Set X} [∀ x, Decidable (x ∈ S)] (f: S → Y): X → Y :=
  fun x => if h: x ∈ S then f ⟨x, h⟩ else Classical.ofNonempty

theorem exists_extension_constructive {X Y: Type*} [Nonempty Y] {S: Set X} [∀ x, Decidable (x ∈ S)] (f: S → Y) (y0: Y):
  Set.restrict S (extension_constructive f y0) = f := by
  sorry

theorem exists_extension_nonconstructive {X Y: Type*} {S: Set X} [Nonempty Y] [∀ x, Decidable (x ∈ S)] (f: S → Y):
  Set.restrict S (fun x => if h: x ∈ S then f ⟨x, h⟩ else Classical.ofNonempty) = f := by
  --classical
  --exact exists_extension_constructive f Classical.ofNonempty
  --exists fun x => if h: x ∈ S then f ⟨x, h⟩ else Classical.ofNonempty
  simp

theorem exists_extension_map {X: Type*} (S: Set X) (Y: Type*) [Nonempty Y]:
  ∃ F: (S → Y) → (X → Y), ∀ u: S → Y, Set.restrict S (F u) = u := by
  exists fun u => Classical.choose (exists_extension u)
  exact fun u => Classical.choose_spec (exists_extension u)

theorem exists_local_map {X Y Z: Type*} {F: (X → Y) → Z} {S: Set X} [Nonempty Y]
  (h: ∀ u v: X → Y, Set.EqOn u v S → F u = F v):
  ∃ f: (S → Y) → Z, ∀ u: X → Y, F u = f (Set.restrict S u) := by
  obtain ⟨G, hG⟩ := exists_extension_map S Y
  exists F ∘ G
  intro u
  apply h
  rw [←Set.restrict_eq_restrict_iff, hG (S.restrict u)]

theorem sliding_block_code_of_continuous_and_equivariant [Monoid T] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] {F: (T → A) → T → B} (h1: Continuous F) (h2: shift_equivariant F): ∃ S: Set T, ∃ f: (S → A) → B, Finite S ∧ F = sliding_block_from f := by
  let Ω := fun u => Classical.choose (exists_neighbor_eqAt_one h1 u)
  let hΩ := fun u => Classical.choose_spec (exists_neighbor_eqAt_one h1 u)
  have: Set.univ ⊆ ⋃ u, eqOn_nhd u (Ω u) := by
    intro u _
    simp
    exists u
    apply eqOn_nhd_self u
  obtain ⟨C, hC⟩ := IsCompact.elim_finite_subcover
    CompactSpace.isCompact_univ
    (fun u => eqOn_nhd u (Ω u))
    (fun u => eqOn_nhd_open u (hΩ u).left)
    this
  simp at hC
  let S := Set.sUnion (Set.image Ω C)
  exists S
  have hC': ∀ x, ∃ x0 ∈ C, x ∈ eqOn_nhd x0 (Ω x0) := by
    apply Set.exists_set_mem_of_union_eq_top
    apply Set.eq_univ_of_univ_subset
    simp
    exact hC
  have: ∀ x ∈ C, Ω x ⊆ S := by
    intro x _
    apply Set.subset_sUnion_of_mem
    exists x
  have: ∀ x y, Set.EqOn x y S → (proj 1) (F x) = (proj 1) (F y) := by
    intro x y h
    obtain ⟨x0, hx0⟩ := hC' x
    simp [proj, ←(hΩ x0).right x hx0.right, (hΩ x0).right y (Set.EqOn.trans hx0.right (Set.EqOn.mono (this x0 hx0.left) h))]
  obtain ⟨f, hf⟩ := exists_local_map this
  exists f
  constructor
  . apply Set.Finite.sUnion
    exact Set.Finite.image Ω (by simp)
    intro _ hΩx
    rw [Set.image] at hΩx
    obtain ⟨x, hx⟩ := hΩx
    rw [←hx.right]
    exact (hΩ x).left
  . exact (local_map_iff F f).mpr ⟨h2, hf⟩

def is_sliding_block [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ S: Set T, ∃ f: (S → A) → B, Finite S ∧ F = sliding_block_from f

theorem curtis_hedlund_lyndon [Monoid T] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (F: (T → A) → T → B): Continuous F ∧ shift_equivariant F ↔ ∃ S: Set T, ∃ f: (S → A) → B, Finite S ∧ F = sliding_block_from f := by
  constructor
  . intro h
    exact sliding_block_code_of_continuous_and_equivariant h.left h.right
  . intro h
    obtain ⟨S, f, hf⟩ := h
    rw [hf.right]
    constructor
    . apply sliding_block_code_continuous f hf.left
    . exact sliding_block_map_equivariant f

theorem uniform_continuous_of_sliding_block_code {A B T: Type*} [Mul T] [UniformSpace A] [UniformSpace B] [DiscreteUniformity A] [DiscreteUniformity B] {S: Set T} (f: (S → A) → B) (h: Finite S): UniformContinuous (sliding_block_from f) := by
  apply prodiscrete_uniform_continuous_iff.mpr
  intro Ω hΩ
  exists setMul Ω S
  constructor
  . apply Set.Finite.image2
    exact hΩ
    exact h
  . simp
    intro _ h'
    exact local_map_eq f h'

theorem sliding_block_code_of_uniform_continuous_and_equivariant [MulOneClass T] [Nonempty A] [UniformSpace A] [DiscreteUniformity A] [UniformSpace B] [DiscreteUniformity B] {F: (T → A) → T → B} (h1: UniformContinuous F) (h2: shift_equivariant F): is_sliding_block F := by
  obtain ⟨S, hS⟩ := prodiscrete_uniform_continuous_iff.mp h1 {1} (Set.finite_singleton 1)
  simp [eqOn_entourage] at hS
  obtain ⟨f, hf⟩ := exists_local_map hS.right
  exists S, f
  constructor
  . exact hS.left
  . ext x t
    simp [sliding_block_from]
    rw [←hf (shift t x), h2, shift_eq]

theorem curtis_hedlund_lyndon_uniform {A B T: Type*} [Monoid T] [Nonempty A] [UniformSpace A] [DiscreteUniformity A] [UniformSpace B] [DiscreteUniformity B] (F: (T → A) → T → B): UniformContinuous F ∧ shift_equivariant F ↔ ∃ S: Set T, ∃ f: (S → A) → B, Finite S ∧ F = sliding_block_from f := by
  constructor
  . intro h
    exact sliding_block_code_of_uniform_continuous_and_equivariant h.left h.right
  . intro h
    obtain ⟨_, f, hf⟩ := h
    rw [hf.right]
    constructor
    . exact uniform_continuous_of_sliding_block_code f hf.left
    . exact sliding_block_map_equivariant f

theorem ShiftSpace_preimage2 {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  {S: Set M} (f: (S → A) → B) (Λ: Set (M → B)) (h2: ShiftSpace Λ):
    ShiftSpace (Set.preimage (sliding_block_from f) Λ) := by
  sorry


theorem ShiftSpace_preimage {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (F: (M → A) → M → B) (Λ: Set (M → B)) (h1: ShiftSpace Λ) (h2: has_finite_local_map F): ShiftSpace (Set.preimage F Λ) :=
  by
  obtain ⟨S, f, hf⟩ := h2
  rw [hf.right]
  constructor
  . apply IsClosed.preimage
    exact sliding_block_code_continuous f hf.left
    exact h1.closed
  . intro _ hx _
    simp
    rw [sliding_block_map_equivariant]
    apply h1.shift_invariant
    exact hx

-- the image of a subshift under a sliding block code is a subshift
/-
theorem ShiftSpace_image {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (M → A) → (M → B)) (h1: sliding_block_code F) (Λ1: Set (M → A)) (h2: ShiftSpace Λ1):
    ShiftSpace (Set.image F Λ1) := by
  have ⟨hF1, hF2⟩ := (curtis_hedlund_lyndon F).mp h1
  constructor
  sorry -- why is the image closed?
  exact shift_invariant_equivariant_image h2.shift_invariant hF2
-/


/--/
theorem ShiftSpace_image2 {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  {S: Set M} (f: (S → A) → B) (Λ: Set (M → A)) (h: ShiftSpace Λ):
  ShiftSpace (Set.image (sliding_block_from f) Λ) := by
  sorry
-/

theorem ShiftSpace_image {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  {S: Set M} (F: (M → A) → M → B) (Λ: Set (M → A)) (h1: ShiftSpace Λ) (h2: is_sliding_block F):
  ShiftSpace (Set.image F Λ) := by
  sorry

-- if T is a monoid and f: A → B then F: A^T → B^T defined by F(x) = f ∘ x is a sliding block code
theorem postcomp_local_map [MulOneClass T] (f: A → B):
  local_map (fun x => f ∘ x) (fun x: ((@Set.singleton T 1) → A) => f (x ⟨1, rfl⟩)) := by
  rw [local_map]
  intro x t
  simp
  rw [shift_eq]

/-
theorem postcomp_memory_set [MulOneClass T] (f: A → B):
  memory_set (fun x => f ∘ x) (@Set.singleton T 1) := by
  rw [memory_set]
  exists fun x: ((@Set.singleton T 1) → A) => f (x ⟨1, rfl⟩)
  exact postcomp_local_map f

theorem sliding_block_code_postcomp [MulOneClass T] (f: A → B):
  sliding_block_code (fun x: T → A => f ∘ x) := by
  exists {1}
  constructor
  exact Set.finite_singleton 1
  exact postcomp_memory_set f
-/

-- 1.45: if A is finite, f: A → B, and X is a subshift ot A^T then (f ∘ x)(X) is a subshift of B^T
theorem sliding_block_code_postcomp_subshift {A B T: Type} [Monoid T] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (X: Set (T → A)) (hX: ShiftSpace X) (f: A → B):
  ShiftSpace (Set.image (fun x => f ∘ x) X) := {
    closed := sorry
    shift_invariant := by
      intro x hx t
      simp_all
      obtain ⟨y, hy⟩ := hx
      sorry
  }

-- 1.46
def equivariant2 {A T Y: Type*} [Mul T]
  [SMul T Y]
  (f: (T → A) → Y): Prop :=
  ∀ x: T → A, ∀ t: T,
  f (shift t x) = t • (f x)

def equivariant3 {X Y T: Type*} [Mul T]
  [SMul T X] [SMul T Y]
  (f: X → Y): Prop :=
  ∀ (x: X) (t: T), f (t • x) = t • (f x)


-- 1.46.a
example {A B T Y: Type*} [Group T]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace Y]
  [TopologicalSpace T]
  [MulAction T Y] [ContinuousSMul T Y]
  {Z: Set Y}
  {f: (T → A) → Y}
  (h1: Set.image2 (fun t z => t • z) (@Set.univ T) Z ⊆ Z)
  (h2: equivariant2 f)
  (h3: Continuous f):
  ShiftSpace (Set.preimage f Z) := sorry

-- 1.46.b
example {A B T Y: Type*} [Group T]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace Y]
  [TopologicalSpace T]
  [T2Space Y]
  [MulAction T Y] [ContinuousSMul T Y]
  {f g: (T → A) → Y}
  (h1: equivariant2 f)
  (h2: Continuous f)
  (h3: equivariant2 g)
  (h4: Continuous g):
  ShiftSpace {x: T → A | f x = g x} := sorry

-- 1.46.c is equivalent to 1.39.f

-- 1.46.d
-- this should probably follow from 1.46.b
theorem eqOn_subshift [Group T]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  {f g: (T → A) → (T → B)}
  (h1: shift_equivariant f)
  (h2: Continuous f)
  (h3: shift_equivariant g)
  (h4: Continuous g):
  ShiftSpace {x: T → A | f x = g x} := {
  closed := sorry
  shift_invariant := sorry
}

-- 1.46.e
example [Group T]
  [TopologicalSpace A] [DiscreteTopology A]
  {f: (T → A) → (T → A)}
  (h1: shift_equivariant f)
  (h2: Continuous f):
  ShiftSpace {x: T → A | f x = x} :=
  eqOn_subshift h1 h2 (shift_equivariant_id) (continuous_id)



-- 1.47
-- 1.48

-- 1.74
-- The language of a configuration A^Z

-- definition of a surjunctive group
/-
def surjunctive (G: Type) [Group G]: Prop :=
  ∀ A: Type, ∀ F: (G → A) → (G → A), Finite A ∧ sliding_block_code F ∧ Function.Injective F → Function.Surjective F
-/
