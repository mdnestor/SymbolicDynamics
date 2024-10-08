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

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Card

-- import Mathlib.Algebra.Group.Pointwise.Set -- causes build to fail?
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.Defs.Basic

import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Separation
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.MulAction

import SymbolicDynamics.ShiftSpace
import SymbolicDynamics.ProdiscreteTopology

open Topology

variable {A B C T : Type*}

-- definition of a "local defining map"

def local_map [Mul T] {S: Set T} (F: (T → A) → T → B) (f: (S → A) → B): Prop :=
  ∀ x: T → A, ∀ t: T, F x t = f (Set.restrict S (shift t x))

def local_map_from [Mul T] {S: Set T} (f: (S → A) → B): (T → A) → T → B :=
  fun x: T → A => fun t: T => f (Set.restrict S (shift t x))

-- definition of a "memory set"
def memory_set [Mul T] (F: (T → A) → T → B) (S: Set T): Prop :=
  ∃ f: (S → A) → B, local_map F f


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
theorem memory_set_univ [MulOneClass T] {F: (T → A) → T → B}
  (hf: shift_equivariant F): memory_set F Set.univ := by
  exists fun x => F (x ∘ (@Equiv.Set.univ T).invFun) 1
  intro _ _
  rw [shift_one_equivariant hf]
  congr

-- if T is a unital magma then {1} is a memory set for the identity on T → X
theorem memory_set_id [MulOneClass T]: memory_set (@id (T → A)) {1} := by
  exists fun x => x ⟨1, rfl⟩
  intro
  simp [leftMul, shift]

-- if S is a memory set and S ⊆ S' then S' is a memory set
-- i.e. memory sets are upward closed
theorem memory_set_incl [Mul T] {F: (T → A) → T → B} {S1 S2: Set T} (h1: memory_set F S1) (h2: S1 ⊆ S2): memory_set F S2 := by
  obtain ⟨f1, hf1⟩ := h1
  exists fun x => f1 (fun ⟨t, ht⟩ => x ⟨t, h2 ht⟩)

def setMul [Mul T] (S1 S2: Set T): Set T :=
  (Set.image2 fun t1 t2 => t1 * t2) S1 S2

-- if F is a sliding block code with memory set S
-- if u and v are equal on Ω * S (pointwise multiplication)
-- then F(u) and F(v) are equal on Ω
theorem memory_set_eq [Mul T] {F: (T → A) → T → B} {S: Set T} (h1: memory_set F S) {x y: T → A} {Ω: Set T} (h2: Set.EqOn x y (setMul Ω S)): Set.EqOn (F x) (F y) Ω := by
  obtain ⟨f, hf⟩ := h1
  intro t hg
  rw [hf x t, hf y t]
  apply congrArg
  simp [Set.EqOn]
  intro t' _
  apply h2
  exists t
  constructor
  assumption
  exists t'

-- definition of sliding block code: there exists a finite memory set
def sliding_block_code [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S

-- sliding block codes are shift-equivariant
theorem sliding_block_code_equivariant [Semigroup T] {F: (T → A) → T → B} (h: sliding_block_code F): shift_equivariant F := by
  obtain ⟨_, _, hS2⟩ := h
  obtain ⟨_, hf⟩ := hS2
  exact local_map_equivariant hf

-- the shift map is a sliding sliding block code
-- TODO: weaken commutativity assumption?
theorem shift_is_sliding_block_code [CommMonoid T] (t: T): sliding_block_code (fun x: T → A => shift t x) := by
  exists {t}
  constructor
  · exact Set.finite_singleton t
  · exists fun x => x ⟨t, Set.mem_singleton t⟩
    intro x g
    simp [shift, leftMul]
    rw [mul_comm]

-- f is a local map for F iff. F is equivariant and ∀ x, F(x)(1) = f (x|S)
theorem local_map_iff [Monoid T] {F: (T → A) → T → B} {S: Set T} (hS: Finite S) (f: (S → A) → B): local_map F f ↔ shift_equivariant F ∧ ∀ u, F u 1 = f (S.restrict u) := by
  constructor
  . intro h
    have h1: sliding_block_code F := by
      rw [sliding_block_code]
      exists S
      constructor
      exact hS
      exists f
    constructor
    exact sliding_block_code_equivariant h1
    intro x
    simp [h x, shift_one]
  . intro ⟨h1, h2⟩ x g
    rw [←h2 (shift g x), h1]
    simp [shift, leftMul]

-- If F1 has local map f1 on S1 and
-- F2 has local map f2 on S2
-- this theorem constructs the corresponding local map of F2 ∘ F1
theorem local_map_compose [Semigroup T] {F1: (T → A) → T → B} {F2: (T → B) → T → C} {S1 S2: Set T}
  {f1: (S1 → A) → B} {f2: (S2 → B) → C} (h1: local_map F1 f1) (h2: local_map F2 f2):
  local_map (F2 ∘ F1) (fun x: setMul S2 S1 → A => f2 (fun s2 => f1 (fun s1 => x ⟨s2.val * s1.val, ⟨s2.val, s2.prop, by exists s1.val; simp⟩⟩))) := by
  intro _ _
  simp [Function.comp]
  rw [h2]
  congr
  ext
  simp_all
  rw [←local_map_equivariant h1, h1]
  congr

-- If F1 has memory set S1 and F2 has memory set S2 then F2 ∘ F1 has memory set S2 * S1
theorem memory_set_compose [Semigroup T] {F1: (T → A) → T → B} {F2: (T → B) → T → C} {S1 S2: Set T} (h1: memory_set F1 S1) (h2: memory_set F2 S2): memory_set (F2 ∘ F1) (setMul S2 S1) := by
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  exists fun x => f2 (fun s2 => f1 (fun s1 => x ⟨s2.val * s1.val, ⟨s2.val, s2.prop, by exists s1.val; simp⟩⟩))
  exact local_map_compose hf1 hf2

-- If F1 and F2 are sliding block codes then F1 ∘ F2 is a sliding block code
theorem sliding_block_code_compose [Semigroup T] {F1: (T → A) → T → B} {F2: (T → B) → T → C}
  (h1: sliding_block_code F1) (h2: sliding_block_code F2): sliding_block_code (F2 ∘ F1) := by
  obtain ⟨S1, hS1⟩ := h1
  obtain ⟨S2, hS2⟩ := h2
  exists setMul S2 S1
  constructor
  . apply Set.Finite.image2
    exact hS2.left
    exact hS1.left
  . exact memory_set_compose hS1.right hS2.right

-- every sliding block code is continuous
theorem sliding_block_code_continuous [MulOneClass T] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] {F: (T → A) → T → B} (h: sliding_block_code F): Continuous F := by
  apply continuous_of_neighborhood_continuous.mpr
  intro x V hV
  obtain ⟨Ω, hΩ⟩ := exists_finite_eqOn_nhd hV
  let ⟨S, hS⟩ := h
  let ΩS := setMul Ω S
  exists eqOn_nhd x ΩS
  apply And.intro
  apply eqOn_nhd_is_nhd x ΩS
  apply Set.Finite.image2
  exact hΩ.left
  exact hS.left
  have h1: Set.image F (eqOn_nhd x ΩS) ⊆ eqOn_nhd (F x) Ω := by
    intro Fy hFy
    simp [eqOn_nhd] at hFy
    obtain ⟨_, hy⟩ := hFy
    simp [eqOn_nhd, ←hy.right]
    exact memory_set_eq hS.right hy.left
  exact le_trans h1 hΩ.right

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

-- if A is nonempty and finite and F: (T → A) → T → B is continuous and equivariant then it is a sliding block code
theorem sliding_block_code_of_continuous_and_equivariant [Monoid T] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] {F: (T → A) → T → B} (h1: Continuous F) (h2: shift_equivariant F): sliding_block_code F := by
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
    (fun u => eqOn_nhd_open u (Ω u) (hΩ u).left)
    this
  simp at hC
  let S := Set.sUnion (Set.image Ω C)
  exists S
  have hS: Finite S := by
    apply Set.Finite.sUnion
    exact Set.Finite.image Ω (by simp)
    intro _ hΩx
    rw [Set.image] at hΩx
    obtain ⟨x, hx⟩ := hΩx
    rw [←hx.right]
    exact (hΩ x).left
  constructor
  exact hS
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
  apply (local_map_iff hS f).mpr
  exact ⟨h2, hf⟩

/-
Curtis-Hedlund-Lyndon theorem:
If A is finite then a map F: (G → A) → (G → A) is a sliding block code iff. it is both equivariant and continuous
-/
theorem curtis_hedlund_lyndon [Monoid T] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (F: (T → A) → T → B): sliding_block_code F ↔ (Continuous F ∧ shift_equivariant F) :=
  ⟨fun h => ⟨sliding_block_code_continuous h, sliding_block_code_equivariant h⟩, fun ⟨h1, h2⟩ => sliding_block_code_of_continuous_and_equivariant h1 h2⟩

theorem uniform_continuous_of_sliding_block_code {A B T: Type*} [Mul T] [UniformSpace A] [UniformSpace B] [DiscreteUniformity A] [DiscreteUniformity B] {F: (T → A) → T → B} (h: sliding_block_code F): UniformContinuous F := by
  apply prodiscrete_uniform_continuous_iff.mpr
  intro Ω hΩ
  obtain ⟨S, hS⟩ := h
  exists setMul Ω S
  constructor
  apply Set.Finite.image2
  exact hΩ
  exact hS.left
  simp
  intro (x, y) hxy
  simp_all [eqOn_entourage]
  exact memory_set_eq hS.right hxy

theorem sliding_block_code_of_uniform_continuous_and_equivariant [MulOneClass T] [Nonempty A] [UniformSpace A] [DiscreteUniformity A] [UniformSpace B] [DiscreteUniformity B] {F: (T → A) → T → B} (h1: UniformContinuous F) (h2: shift_equivariant F): sliding_block_code F := by
  obtain ⟨S, hS⟩ := prodiscrete_uniform_continuous_iff.mp h1 {1} (Set.finite_singleton 1)
  exists S
  constructor
  exact hS.left
  simp [eqOn_entourage] at hS
  obtain ⟨f, hf⟩ := exists_local_map hS.right
  exists f
  intro x t
  rw [←hf (shift t x), h2]
  simp [shift_eq]

-- drops the finite assumption
theorem curtis_hedlund_lyndon_uniform {A B T: Type*} [Monoid T] [Nonempty A] [UniformSpace A] [DiscreteUniformity A] [UniformSpace B] [DiscreteUniformity B] (F: (T → A) → T → B): sliding_block_code F ↔ (UniformContinuous F ∧ shift_equivariant F) := by
  apply Iff.intro
  exact fun h => ⟨uniform_continuous_of_sliding_block_code h, sliding_block_code_equivariant h⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_uniform_continuous_and_equivariant h1 h2

-- the preimage of a subshift under a sliding block code is a subshift
-- may hold when A is not necessarily finite
theorem Subshift_preimage {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (M → A) → (M → B)) (h1: sliding_block_code F) (Λ: Set (M → B)) (h2: Subshift Λ):
    Subshift (Set.preimage F Λ) := by
  have ⟨hF1, hF2⟩ := (curtis_hedlund_lyndon F).mp h1
  constructor
  apply IsClosed.preimage hF1 closed
  intro _ hx _
  simp
  rw [hF2]
  apply shift_invariant
  exact hx

-- the image of a subshift under a sliding block code is a subshift
theorem Subshift_image {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (M → A) → (M → B)) (h1: sliding_block_code F) (Λ1: Set (M → A)) (h2: Subshift Λ1):
    Subshift (Set.image F Λ1) := by
  have ⟨hF1, hF2⟩ := (curtis_hedlund_lyndon F).mp h1
  constructor
  sorry -- why is the image closed?
  exact shift_invariant_equivariant_image h2.shift_invariant hF2

-- if T is a monoid and f: A → B then F: A^T → B^T defined by F(x) = f ∘ x is a sliding block code
theorem postcomp_local_map [MulOneClass T] (f: A → B):
  local_map (fun x => f ∘ x) (fun x: ((@Set.singleton T 1) → A) => f (x ⟨1, rfl⟩)) := by
  rw [local_map]
  intro x t
  simp
  rw [shift_eq]

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

-- 1.45: if A is finite, f: A → B, and X is a subshift ot A^T then (f ∘ x)(X) is a subshift of B^T
theorem sliding_block_code_postcomp_subshift {A B T: Type} [Monoid T] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (X: Set (T → A)) (hX: Subshift X) (f: A → B):
  Subshift (Set.image (fun x => f ∘ x) X) := {
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
  Subshift (Set.preimage f Z) := sorry

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
  Subshift {x: T → A | f x = g x} := sorry

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
  Subshift {x: T → A | f x = g x} := sorry

-- 1.46.e
example [Group T]
  [TopologicalSpace A] [DiscreteTopology A]
  {f: (T → A) → (T → A)}
  (h1: shift_equivariant f)
  (h2: Continuous f):
  Subshift {x: T → A | f x = x} :=
  eqOn_subshift h1 h2 (shift_equivariant_id) (continuous_id)



-- 1.47
-- 1.48

-- 1.74
-- The language of a configuration A^Z

-- definition of a surjunctive group
def surjunctive (G: Type) [Group G]: Prop :=
  ∀ A: Type, ∀ F: (G → A) → (G → A), Finite A ∧ sliding_block_code F ∧ Function.Injective F → Function.Surjective F
