/-

Main reults:

-- defines the shift map and proves it is continuous
-- defines sliding block code
-- proves the Curtis–Hedlund–Lyndon (CHL) theorem
-- defines subshifts

Notation
-- A, B, C for alphabets, T for tape positions equipped with some algebraic structure
-- results are general as possible, some use `MulOneClass` aka unital magma
-- x, y, z for tape configurations

TODO:

-- prove CHL theorem from the uniform variant (likely simpler proof)
-- variant of CHL theorem for subshifts
-- characterize subshifts in terms of forbidden blocks
-- shifts of finite type
-- sofic shifts

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

import SymbolicDynamics.ProdiscreteTopology

open Topology

variable {A B C T : Type*}

-- results about the shift map
def shift [Mul T] (t: T): (T → A) → (T → A) :=
  fun x => x ∘ leftMul t

-- these could likely be compressed
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

theorem shift_continuous [Mul T] (t: T) [TopologicalSpace A] [DiscreteTopology A]:
  Continuous[Pi.topologicalSpace, Pi.topologicalSpace] (fun x: T → A => shift t x) := by
  rw [pi_generateFrom_cylinders]
  apply continuous_generateFrom_iff.mpr
  intro V
  simp
  intro x U hV
  rw [hV, shift_preimage_cylinder_eq]
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  simp

-- F is equivariant if it commutes with the shift
def equivariant [Mul T] (F: (T → A) → T → B): Prop :=
  ∀ u t, F (shift t u) = shift t (F u)

theorem shift_one_equivariant [MulOneClass T] {F: (T → A) → T → B} {x: T → A} {t: T}
  (hf: equivariant F): F x t = F (shift t x) 1 := by
  calc
    F x t = F x (t * 1) := by rw [mul_one]
        _ = ((F x) ∘ (leftMul t)) 1 := by rfl
        _ = (shift t (F x)) 1 := by rfl
  rw [hf]

def local_map [Mul T] {S: Set T} (F: (T → A) → T → B) (f: (S → A) → B): Prop :=
  ∀ x t, F x t = f (Set.restrict S (shift t x))

-- if F has a local map then it is equivariant
theorem local_map_equivariant [Semigroup T] {S: Set T} {F: (T → A) → T → B} {f: (S → A) → B}
  (h: local_map F f): equivariant F := by
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

def memory_set [Mul T] (F: (T → A) → T → B) (S: Set T): Prop :=
  ∃ f: (S → A) → B, local_map F f

-- if F is equivariant and T is a unital magma then the universe is a memory set
def memory_set_univ [MulOneClass T] {F: (T → A) → T → B}
  (hf: equivariant F): memory_set F Set.univ := by
  exists fun x => F (x ∘ (@Equiv.Set.univ T).invFun) 1
  intro _ _
  rw [shift_one_equivariant hf]
  congr

-- if T is a unital magma then {1} is a memory set for the identity on T → X
def memory_set_id [MulOneClass T]: memory_set (@id (T → A)) {1} := by
  exists fun x => x ⟨1, rfl⟩
  intro
  simp [leftMul, shift]

-- memory sets are upward closed
def memory_set_incl [Mul T] {F: (T → A) → T → B} {S1 S2: Set T} (h1: memory_set F S1) (h2: S1 ⊆ S2): memory_set F S2 := by
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
-- todo: generalize to shift spaces besides the full shit spaces
def sliding_block_code [Mul T] (F: (T → A) → T → B): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S

theorem equivariant_compose [Mul T] {F1: (T → A) → T → B} {F2: (T → B) → T → C} (h1: equivariant F1) (h2: equivariant F2): equivariant (F2 ∘ F1) := by
  simp [equivariant]
  intros
  rw [h1, h2]

theorem sliding_block_equivariant [Semigroup T] {F: (T → A) → T → B} (h: sliding_block_code F): equivariant F := by
  obtain ⟨_, _, hS2⟩ := h
  obtain ⟨_, hf⟩ := hS2
  exact local_map_equivariant hf

-- f is a local map for F iff. F is equivariant and ∀ x, F(x)(1) = f (x|S)
theorem local_map_iff [Monoid T] {F: (T → A) → T → B} {S: Set T} (hS: Finite S) (f: (S → A) → B): local_map F f ↔ equivariant F ∧ ∀ u, F u 1 = f (S.restrict u) := by
  constructor
  . intro h
    have h1: sliding_block_code F := by
      rw [sliding_block_code]
      exists S
      constructor
      exact hS
      exists f
    constructor
    exact sliding_block_equivariant h1
    intro x
    simp [h x, shift_one]
  . intro ⟨h1, h2⟩ x g
    rw [←h2 (shift g x), h1]
    simp [shift, leftMul]

-- if F1 has memory set S1
-- and F2 has memory set S2
-- then F2 ∘ F1 has memory set S1 * S2
theorem memory_set_compose [Mul T] {F1: (T → A) → T → B} {F2: (T → B) → T → C} {S1 S2: Set T} (h1: memory_set F1 S1) (h2: memory_set F2 S2): memory_set (F2 ∘ F1) (setMul S1 S2) := by
    obtain ⟨f1, hf1⟩ := h1
    obtain ⟨f2, hf2⟩ := h2
    -- need a map from ((S1*S2) → A) → C
    sorry

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

-- if A is nonempty and finite and F: (T → A) → T → B is continuous and equivariant then it is a sliding block
theorem sliding_block_code_of_continuous_and_equivariant [Monoid T] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] {F: (T → A) → T → B} (h1: Continuous F) (h2: equivariant F): sliding_block_code F := by
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
theorem curtis_hedlund_lyndon [Monoid T] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (F: (T → A) → T → B): sliding_block_code F ↔ (Continuous F ∧ equivariant F) :=
  ⟨fun h => ⟨sliding_block_code_continuous h, sliding_block_equivariant h⟩, fun ⟨h1, h2⟩ => sliding_block_code_of_continuous_and_equivariant h1 h2⟩

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

theorem sliding_block_code_of_uniform_continuous_and_equivariant [MulOneClass T] [Nonempty A] [UniformSpace A] [DiscreteUniformity A] [UniformSpace B] [DiscreteUniformity B] {F: (T → A) → T → B} (h1: UniformContinuous F) (h2: equivariant F): sliding_block_code F := by
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
theorem curtis_hedlund_lyndon_uniform {A B T: Type*} [Monoid T] [Nonempty A] [UniformSpace A] [DiscreteUniformity A] [UniformSpace B] [DiscreteUniformity B] (F: (T → A) → T → B): sliding_block_code F ↔ (UniformContinuous F ∧ equivariant F) := by
  apply Iff.intro
  exact fun h => ⟨uniform_continuous_of_sliding_block_code h, sliding_block_equivariant h⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_uniform_continuous_and_equivariant h1 h2

class Subshift {M A: Type*} [Mul M] [TopologicalSpace A] (S: Set (M → A)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ g: M, shift g x ∈ S

export Subshift (closed shift_invariant)

theorem Subshift_empty {M A: Type*} [Mul M] [TopologicalSpace A]:
  Subshift (∅: Set (M → A)) := by
  constructor <;> simp

theorem Subshift_univ {M A: Type*} [Mul M] [TopologicalSpace A]:
  Subshift (Set.univ (α := M → A)) := by
  constructor <;> simp

-- artbirary intersections of Subshifts are Subshifts
theorem Subshift_sInter {M A: Type*} [Mul M] [TopologicalSpace A]
  (Λs: Set (Set (M → A))) (h: ∀ Λ ∈ Λs, Subshift Λ): Subshift (Set.sInter Λs) := by
  constructor
  apply isClosed_sInter
  intro Λ hΛ
  exact (h Λ hΛ).1
  intro x hx g Λ hΛ
  exact (h Λ hΛ).2 x (hx Λ hΛ) g

theorem Subshift_iInter {M A: Type*} [Mul M] [TopologicalSpace A]
  {I: Type*} (Λ: I → (Set (M → A))) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iInter Λ) := by
  constructor
  apply isClosed_iInter
  intro i
  exact (h i).1
  intro x hx g Λ hΛ
  simp at hx
  obtain ⟨i, hi⟩ := hΛ
  rw [←hi]
  exact (h i).2 x (hx i) g

theorem Subshift_iUnion {M A: Type*} [Mul M] [TopologicalSpace A] [DiscreteTopology A]
  {I: Type*} [Finite I] (Λ: I → Set (M → A)) (h: ∀ i: I, Subshift (Λ i)): Subshift (Set.iUnion Λ) := by
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
theorem Subshift_preimage {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (M → A) → (M → B)) (h: sliding_block_code F) (Λ2: Set (M → B)) [Subshift Λ2]:
    Subshift (Set.preimage F Λ2) := by
  have ⟨hF1, hF2⟩ := (curtis_hedlund_lyndon F).mp h
  constructor
  apply IsClosed.preimage
  exact hF1
  exact closed
  intro x hx g

  simp [shift]
  sorry
  /-
  rw [hF2]
  exact shift_invariant (F x) hx g
  -/

-- the image of a subshift under a sliding block is a subshift
theorem Subshift_image {M A B: Type*} [Monoid M] [Nonempty A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
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
  sorry
  -- rw [hF2, hy2]


-- a "block" consists of a subset S ⊆ T and a function b: S → A

-- a configuration x: T → A contains a block b if there exists t ∈ T such that
-- S.restrict (shift t x) = f
def contains_block [Mul T] (x: T → A) {S: Set T} (b: S → A): Prop :=
  ∃ t: T, S.restrict (shift t x) = b

-- suppose T is a group
-- if x contains a block b then shift t x contains b
def contains_block_shift [Group T] {x: T → A} {S: Set T} {b: S → A}
  (h: contains_block x b) (t: T): contains_block (shift t x) b := by
  obtain ⟨t', ht'⟩ := h
  exists t⁻¹ * t'
  simp [shift_comp]
  exact ht'

def shift_invariant_of_forbidden_words [Group T] [TopologicalSpace A] (Λ: Set (T → A)):
  (∃ ι: Type, ∃ S: ι → Set T, ∃ b: (i: ι) → (S i → A), Λ = {x: T → A | ∀ i: ι, ¬ contains_block x (b i)})
  → (∀ x ∈ Λ, ∀ t: T, shift t x ∈ Λ) := by
  intro h
  obtain ⟨ι, S, b, h1⟩ := h
  intro x hx t
  rw [h1]
  intro i
  simp [h1] at hx
  specialize hx i
  intro hx'
  have := contains_block_shift hx' t⁻¹
  simp [shift_comp, shift_one] at this
  contradiction


def subshift_iff [Mul T] [TopologicalSpace A] (Λ: Set (T → A)):
  Subshift Λ ↔ ∃ ι: Type, ∃ S: ι → Set T, ∃ b: (i: ι) → (S i → A), Λ = {x: T → A | ∀ i: ι, ¬ contains_block x (b i)} := by
  constructor
  sorry
  sorry
