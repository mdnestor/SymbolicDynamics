/-

Curtis–Hedlund–Lyndon theorem

References

-- "Cellular automata and groups" by Ceccherini-Silberstein and Coornaert (2010)
-- "A note on the definition of sliding block codes and the Curtis-Hedlund-Lyndon Theorem" by Sobottka and Goçcalves (2017) https://arxiv.org/abs/1507.02180
-- "Some notes on the classification of shift spaces: Shifts of Finite Type; Sofic Shifts; and Finitely Defined Shifts" by Sobottka (2020) https://arxiv.org/abs/2010.10595
-- "Symbolic dynamics" on Scholarpedia http://www.scholarpedia.org/article/Symbolic_dynamics

todo: cleanup notation
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

-- definition of sliding block code based on definition 1.4.1

def local_map {A B T: Type} [Mul T] {S: Set T} (F: (T → A) → T → B) (f: (S → A) → B): Prop :=
  ∀ x: T → A, ∀ t: T, F x t = f (Set.restrict S (x ∘ (leftMul t)))

def memory_set {T X Y: Type} [Mul T] (F: (T → X) → T → Y) (S: Set T): Prop :=
  ∃ f: (S → X) → Y, local_map F f

-- definition of sliding block code: there exists a finite memory set
-- todo: generalize to shift spaces besides the full shit spaces
def sliding_block_code {T X Y: Type} [Mul T] (F: (T → X) → T → Y): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S

def equivariant {T X Y: Type} [Mul T] (F: (T → X) → T → Y): Prop :=
  ∀ u: T → X, ∀ t: T, F (u ∘ leftMul t) = F u ∘ leftMul t

def equivariant_compose {T X Y Z: Type} [Mul T]
  {F1: (T → X) → T → Y} {F2: (T → Y) → T → Z}
  (h1: equivariant F1) (h2: equivariant F2):
  equivariant (F2 ∘ F1) := by
  simp [equivariant]
  intros
  rw [h1, h2]

lemma leftMul_comp {T: Type} [Semigroup T] {t1 t2: T}: leftMul t1 ∘ leftMul t2 = leftMul (t1 * t2) := by
  ext
  simp [leftMul, mul_assoc]

theorem sliding_block_equivariant {T X Y: Type} [Semigroup T] {F: (T → X) → T → Y} (h: sliding_block_code F): equivariant F := by
  intro u t
  obtain ⟨S, _, f, hf⟩ := h
  ext t'
  simp [
    hf (u ∘ leftMul t) t',
    Function.comp.assoc,
    leftMul_comp,
    ←hf u (t * t'),
    leftMul
  ]

def setMul [Mul T] (S1 S2: Set T) : Set T :=
  (Set.image2 fun t1 t2 => t1 * t2) S1 S2

-- if F is a sliding block code with memory set S
-- if u and v are equal on Ω * S (pointwise multiplication)
-- then F(u) and F(v) are equal on Ω
theorem memory_set_eq {T X Y: Type} [Mul T]
  {F: (T → X) → T → Y}
  {S: Set T} (h1: memory_set F S)
  {u v: T → X} {Ω: Set T} (h2: Set.EqOn u v (setMul Ω S)):
    Set.EqOn (F u) (F v) Ω := by
  obtain ⟨f, hf⟩ := h1
  intro t hg
  rw [hf u t, hf v t]
  apply congrArg
  simp [Set.EqOn]
  intro t' _
  apply h2
  exists t
  constructor
  assumption
  exists t'

lemma leftMul_one {T X: Type} {u: T → X} [Monoid T]: u ∘ leftMul 1 = u := by
  ext
  simp [leftMul]

lemma eval_at_one {T X Y: Type} [Monoid T] {F: (T → X) → T → Y}
  (u: T → X) (t: T) (h: equivariant F): F u t = F (u ∘ leftMul t) 1 := by
  rw [h]
  simp [leftMul]

-- f is a local map for F iff. F is equivariant and ∀ x, F(x)(1) = f (x|S)
theorem local_map_iff {T X Y: Type} [Monoid T]
  {F: (T → X) → T → Y} {S: Set T} (hS: Finite S) (f: (S → X) → Y):
  local_map F f ↔ equivariant F ∧ ∀ u: T → X, F u 1 = f (Set.restrict S u) := by
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
    simp [h x, leftMul_one]
  . intro ⟨h1, h2⟩ x g
    rw [←h2 (x ∘ leftMul g), h1]
    simp [leftMul]

/-
-- composition of two sliding block codes is a sliding block code
theorem sliding_block_compose {G A: Type} [Mul G]
  {F1: (G → A) → G → A} {F2: (G → A) → G → A}
  {S1 S2: Set G} (h1: memory_set F1 S1) (h2: memory_set F2 S2):
  memory_set (F2 ∘ F1) (setMul S1 S2) := by
    obtain ⟨hS1, f1, hf1⟩ := h1
    obtain ⟨hS2, f2, hf2⟩ := h2
    constructor
    apply Set.Finite.image2
    exact hS1
    exact hS2
    sorry
-/

-- every sliding block code is continuous
theorem sliding_block_code_continuous {T X Y: Type} [Monoid T] [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y]
  {F: (T → X) → T → Y} (h: sliding_block_code F): Continuous F := by
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

-- helper lemmas
theorem exists_neighbor_eqAt_one {T X Y: Type} [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y] [Monoid T] {F: (T → X) → T → Y} (h: Continuous F):
  ∀ u: T → X, ∃ Ω: Set T, Finite Ω ∧ ∀ v: T → X, v ∈ neighbors u Ω → F u 1 = F v 1 := by
    let φ := proj 1 ∘ F
    have hφ : Continuous φ := Continuous.comp (continuous_apply 1) h
    intro u
    have hU: {φ u} ∈ nhds (φ u) := by simp
    obtain ⟨V, hV1, hV2⟩ := continuous_of_neighborhood_continuous.mp hφ u {φ u} hU
    have h4 := (neighbors_forms_neighborhood_base u).2
    specialize h4 V hV1
    obtain ⟨U, hU1, hU2⟩ := h4
    simp_all
    obtain ⟨Ω, hΩ1, hΩ2⟩ := hU1
    exists Ω
    constructor
    exact hΩ1
    intro v hv
    rw [← hΩ2] at hv
    calc
      F u 1 = φ u := by rfl
          _ = φ v := by rw [Eq.symm ((hV2 v) (hU2 hv))]
          _ = F v 1 := by rfl

theorem exists_extension {X Y: Type} {S: Set X} [Nonempty Y]:
  ∀ f: S → Y, ∃ F: X → Y, Set.restrict S F = f := by
  classical -- ensures decidable membership of S
  intro f
  exists fun x => if h: x ∈ S then f ⟨x, h⟩ else Classical.ofNonempty
  simp

theorem exists_extension_map {X: Type} (S: Set X) (Y: Type) [Nonempty Y]:
  ∃ F: (S → Y) → (X → Y), ∀ u: S → Y, Set.restrict S (F u) = u := by
  exists fun u => Classical.choose (exists_extension u)
  intro u
  exact Classical.choose_spec (exists_extension u)

theorem exists_local_map {X Y Z: Type} {F: (X → Y) → Z} {S: Set X} [Nonempty Y]
  (h: ∀ u v: X → Y, Set.EqOn u v S → F u = F v):
  ∃ F': (S → Y) → Z, ∀ u: X → Y, F u = F' (Set.restrict S u) := by
  obtain ⟨G, hG⟩ := exists_extension_map S Y
  exists F ∘ G
  intro u
  apply h
  rw [←Set.restrict_eq_restrict_iff, hG (S.restrict u)]

-- if X is finite and F: (T → X) → T → Y is continuous and equivariant then it is a sliding block
theorem sliding_block_code_of_continuous_and_equivariant {T X Y: Type} [Monoid T] [Finite X] [Nonempty X] [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y] {F: (T → X) → T → Y}
  (h1: Continuous F) (h2: equivariant F): sliding_block_code F := by
  have h3: ∃ Ω: (T → X) → Set T, ∀ u: T → X, Finite (Ω u) ∧ ∀ v: T → X, v ∈ neighbors u (Ω u) → F u 1 = F v 1 := by
    exists fun u => Classical.choose (exists_neighbor_eqAt_one h1 u)
    exact fun u => Classical.choose_spec (exists_neighbor_eqAt_one h1 u)
  obtain ⟨Ω, hΩ⟩ := h3
  have h4 : ∀ u, Finite (Ω u) := fun u => (hΩ u).1
  have h5 : Set.univ ⊆ ⋃ u, neighbors u (Ω u) := by
    intro u _
    simp
    exists u
    apply neighbors_self u
  obtain ⟨C, hC⟩ := IsCompact.elim_finite_subcover CompactSpace.isCompact_univ (fun u => neighbors u (Ω u)) (fun u => neighbors_open u (Ω u) (h4 u)) h5
  simp at hC
  let S := Set.sUnion (Set.image Ω C)
  exists S
  have h6 : Finite S := by
    apply Set.Finite.sUnion
    exact Set.Finite.image Ω (by simp)
    intro _ hΩx
    rw [Set.image] at hΩx
    obtain ⟨x, hx⟩ := hΩx
    rw [←hx.2]
    exact h4 x
  constructor
  exact h6
  have h7: ∀ x: T → X, ∃ x0 ∈ C, x ∈ neighbors x0 (Ω x0) := by
    apply Set.exists_set_mem_of_union_eq_top
    apply Set.eq_univ_of_univ_subset
    simp
    exact hC
  have h8: ∀ x ∈ C, Ω x ⊆ S := by
    intro x _
    apply Set.subset_sUnion_of_mem
    exists x
  have h9: ∀ x y: T → X, Set.EqOn x y S → (proj 1) (F x) = (proj 1) (F y) := by
    intro x y h
    obtain ⟨x0, hx01, hx02⟩ := h7 x
    simp [proj, ←(hΩ x0).2 x hx02, (hΩ x0).2 y (Set.EqOn.trans hx02 (Set.EqOn.mono (h8 x0 hx01) h))]
  obtain ⟨f, hf⟩ := exists_local_map h9
  exists f
  apply (local_map_iff h6 f).mpr
  exact ⟨h2, hf⟩

/-
Curtis-Hedlund-Lyndon theorem:
If A is finite then a map F: (G → A) → (G → A) is a sliding block code iff. it is both equivariant and continuous
-/
theorem curtis_hedlund_lyndon {G A: Type} [Monoid G] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  (F: (G → A) → G → B):
  sliding_block_code F ↔ (Continuous F ∧ equivariant F) := by
  constructor
  exact fun h => ⟨sliding_block_code_continuous h, sliding_block_equivariant h⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_continuous_and_equivariant h1 h2

/-
theorem uniform_continuous_of_sliding_block_code {G A: Type} [Group G] [UniformSpace A] {F: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: sliding_block_code F): UniformContinuous F :=
  sorry

theorem sliding_block_code_of_uniform_continuous_and_equivariant {G A: Type} [Group G] [UniformSpace A] {F: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: UniformContinuous F) (h2:equivariant F): sliding_block_code F :=
  sorry

-- drops the finite assumption
theorem curtis_hedlund_lyndon_uniform {G A: Type} [Group G] [UniformSpace A] (h: uniformity A = Filter.principal idRel) (F: (G → A) → G → A): sliding_block_code F ↔ (UniformContinuous F ∧ equivariant F) := by
  apply Iff.intro
  exact fun h1 => ⟨uniform_continuous_of_sliding_block_code h h1, sliding_block_equivariant h1⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_uniform_continuous_and_equivariant h h1 h2
-/
