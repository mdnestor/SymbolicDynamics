/-

some alternative definitions using monoid actions

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Card

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
  (F: (X → Y) → X → Z) (f: (S → Y) → Z): Prop :=
  ∀ u: X → Y, ∀ x: X, F u x = f (fun t => u (t.val • x))

-- requires a commutative monoid.. can this be weakened?
theorem local_map_implies_equivariant {T X Y Z: Type} [CommMonoid T] [MulAction T X] {S: Set T}
  (F: (X → Y) → X → Z) (f: (S → Y) → Z) (h: local_map F f): equivariant T F := by
  intro u t
  ext x
  rw [h (fun x ↦ u (t • x)) x]
  rw [h u (t • x)]
  apply congrArg
  ext
  repeat rw [←mul_smul]
  rw [mul_comm]

def memory_set {T X Y Z: Type} [Monoid T] [MulAction T X] (F: (X → Y) → X → Z) (S: Set T): Prop :=
  ∃ f: (S → Y) → Z, local_map F f

def sliding_block_code {X Y Z: Type} (T: Type) [Monoid T] [MulAction T X]
  (F: (X → Y) → X → Z): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S

def setMul  {T X: Type} [Monoid T] [MulAction T X] (S: Set T) (Ω: Set X) : Set X :=
  (Set.image2 fun t x => t • x) S Ω

theorem memory_set_eq {T X Y Z: Type} [Monoid T] [MulAction T X] (F: (X → Y) → X → Z) (S: Set T)
  (h: memory_set F S) {u v: X → Y} {Ω: Set X} (h2: Set.EqOn u v (setMul S Ω)):
    Set.EqOn (F u) (F v) Ω := by
  obtain ⟨f, hf⟩ := h
  intro x hx
  rw [hf u x, hf v x]
  apply congrArg
  ext ⟨t, ht⟩
  apply h2
  exists t
  constructor
  exact ht
  exists x

/-
theorem local_map_iff {T X Y Z: Type} [Monoid T] [MulAction T X] (F: (X → Y) → X → Z) (S: Set T)
  {F: (X → Y) → X → Z} {S: Set G} (hS: Finite S) (μ: (S → A) → A):
  local_map τ μ ↔ equivariant τ ∧ ∀ x: G → A, τ x 1 = μ (Set.restrict S x) := by
  constructor
  . intro h
    have h1: sliding_block_code τ := by
      rw [sliding_block_code]
      exists S
      constructor
      exact hS
      exists μ
    constructor
    exact sliding_block_equivariant h1
    intro x
    simp [h x, leftMul_one]
  . intro ⟨h1, h2⟩ x g
    rw [←h2 (x ∘ leftMul g), h1]
    simp [leftMul]
-/

theorem sliding_block_code_continuous {T X Y Z: Type} [Monoid T] [MulAction T X] [Finite Y] [Nonempty Y] [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Z] [DiscreteTopology Z] {F: (X → Y) → X → Z}
  {F: (X → Y) → X → Z} (h: sliding_block_code T F): Continuous F := by
  apply continuous_of_neighborhood_continuous.mpr
  intro u V hV
  obtain ⟨Ω, hΩ1, hΩ2⟩ := neighbor_lemma hV
  let ⟨S, hS1, hS2⟩ := h
  let ΩS := setMul Ω S
  exists neighbors u ΩS
  apply And.intro
  apply neighbors_is_nhd u ΩS
  apply Set.Finite.image2
  exact hΩ1
  exact hS1
  have h1: Set.image F (neighbors u ΩS) ⊆ neighbors (F u) Ω := by
    intro Fy hFy
    simp [neighbors] at hFy
    obtain ⟨v, hv1, hv2⟩ := hFy
    simp [neighbors, ←hv2]
    exact memory_set_eq hS2 hv1
  exact le_trans h1 hΩ2


-- if X is nonempty and finite and F: (T → X) → T → Y is continuous and equivariant then it is a sliding block
theorem sliding_block_code_of_continuous_and_equivariant {T X Y Z: Type} [Monoid T] [MulAction T X] [Finite Y] [Nonempty Y] [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Z] [DiscreteTopology Z] {F: (X → Y) → X → Z}
  (h1: Continuous F) (h2: equivariant T F): sliding_block_code T F := by
  sorry

theorem curtis_hedlund_lyndon {T X Y Z: Type} [Monoid T] [MulAction T X] [Finite Y] [Nonempty Y] [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Z] [DiscreteTopology Z]
  (F: (X → Y) → (X → Z)):
  sliding_block_code T F ↔ (Continuous F ∧ equivariant T F) := by
  sorry

-- generalizes the other version since a monoid acts on itself via multiplication
theorem curtis_hedlund_lyndon_ver2 {T Y Z: Type} [Monoid T] [Finite Y] [Nonempty Y] [TopologicalSpace Y] [DiscreteTopology Y] [TopologicalSpace Z] [DiscreteTopology Z]
  (F: (T → Y) → (T → Z)):
  sliding_block_code T F ↔ (Continuous F ∧ equivariant T F) :=
  curtis_hedlund_lyndon F
