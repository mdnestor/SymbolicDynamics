/-

Curtis–Hedlund–Lyndon theorem

References

-- "Cellular automata and groups" by Ceccherini-Silberstein and Coornaert (2010)
-- "A note on the definition of sliding block codes and the Curtis-Hedlund-Lyndon Theorem" by Sobottka and Goçcalves (2017) https://arxiv.org/abs/1507.02180
-- "Some notes on the classification of shift spaces: Shifts of Finite Type; Sofic Shifts; and Finitely Defined Shifts" by Sobottka (2020) https://arxiv.org/abs/2010.10595
-- "Symbolic dynamics" on Scholarpedia http://www.scholarpedia.org/article/Symbolic_dynamics

TODO: correct shift space, use Finsets
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

-- definition of sliding block code based on definition 1.4.1

def local_map {G A B: Type} [Mul G] {S: Set G} (τ: (G → A) → G → B) (μ: (S → A) → B): Prop :=
  ∀ x: G → A, ∀ g: G, τ x g = μ (Set.restrict S (x ∘ (leftMul g)))

def memory_set {G A B: Type} [Mul G] (τ: (G → A) → G → B) (S: Set G): Prop :=
  Finite S ∧ ∃ μ: (S → A) → B, local_map τ μ

def memory_finset {G A B: Type} [Mul G] (τ: (G → A) → G → B) (S: Finset G): Prop :=
  ∃ μ: (S → A) → B, local_map τ μ

def shift_space {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A] (S: Set (M → A)): Prop :=
  IsClosed S ∧ ∀ x ∈ S, ∀ g: M, x ∘ leftMul g ∈ S

def window {A M: Type} (Λ: Set (M → A)) (N: Set M): Set (N → A) :=
  {w: N → A | ∃ x ∈ Λ, w = Set.restrict N x}

def sliding_block_code {A B M: Type} [Mul M] (Φ: (M → A) → M → B): Prop :=
  ∃ S: Set M, memory_set Φ S

def sliding_block_code_fin {A B M: Type} [Mul M] (Φ: (M → A) → M → B): Prop :=
  ∃ S: Finset M, memory_finset Φ S

def sliding_block_code_correct {A B M: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A] {Λ: Set (M → A)} (h: shift_space Λ) (Φ: Λ → M → B): Prop :=
  sorry

def equivariant {G A B: Type} [Mul G] (τ: (G → A) → G → B): Prop :=
  ∀ x: G → A, ∀ g: G, τ (x ∘ leftMul g) = τ x ∘ leftMul g

def equivariant_compose {G A B C: Type} [Mul G]
  {τ1: (G → A) → G → B} {τ2: (G → B) → G → C}
  (h1: equivariant τ1) (h2: equivariant τ2):
  equivariant (τ2 ∘ τ1) := by
  simp [equivariant]
  intros
  rw [h1, h2]

lemma leftMul_comp {G: Type} [Semigroup G] {g g': G}: leftMul g ∘ leftMul g' = leftMul (g * g') := by
  ext
  simp [leftMul, mul_assoc]

theorem sliding_block_equivariant {G A: Type} [Semigroup G] {τ: (G → A) → G → B} (h: sliding_block_code τ): equivariant τ := by
  intro x g
  obtain ⟨S, _, μ, hμ⟩ := h
  ext g'
  simp [
    hμ (x ∘ leftMul g) g',
    Function.comp.assoc,
    leftMul_comp,
    ←hμ x (g * g'),
    leftMul
  ]

def setMul [Mul G] (A B: Set G) : Set G :=
  (Set.image2 fun x y => x * y) A B

-- if τ is a sliding block code with memory set S
-- if x and y are equal on Ω * S (pointwise multiplication)
-- then τ(x) and τ(y) are equal on Ω
theorem memory_set_eq {G A: Type} [Mul G]
  {τ: (G → A) → G → A}
  {S: Set G} (h1: memory_set τ S)
  {x y: G → A} {Ω: Set G} (h2: Set.EqOn x y (setMul Ω S)):
    Set.EqOn (τ x) (τ y) Ω := by
  obtain ⟨_, μ, hμ⟩ := h1
  intro g hg
  rw [hμ x g, hμ y g]
  apply congrArg
  simp [Set.EqOn]
  intro g' _
  apply h2
  exists g
  constructor
  assumption
  exists g'

lemma leftMul_one {G A: Type} {x: G → A} [Monoid G]: x ∘ leftMul 1 = x := by
  ext
  simp [leftMul]

lemma eval_at_one {G A: Type} [Group G] {τ: (G → A) → G → A}
  (x: G → A) (g: G) (h: equivariant τ): τ x g = τ (x ∘ leftMul g) 1 := by
  rw [h]
  simp [leftMul]

-- proposition 1.4.6
theorem cellular_automata_iff {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A]
  {τ: (G → A) → G → A} {S: Set G} (hS: Finite S) (μ: (S → A) → A):
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

theorem sliding_block_compose {G A: Type} [Mul G]
  {τ1: (G → A) → G → A} {τ2: (G → A) → G → A}
  {S1 S2: Set G} (h1: memory_set τ1 S1) (h2: memory_set τ2 S2):
  memory_set (τ2 ∘ τ1) (setMul S1 S2) := by
    obtain ⟨hS1, μ1, hμ1⟩ := h1
    obtain ⟨hS2, μ2, hμ2⟩ := h2
    constructor
    apply Set.Finite.image2
    exact hS1
    exact hS2
    sorry

-- proposition 1.4.8
theorem sliding_block_code_continuous {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A]
  {τ: (G → A) → G → A} (h: sliding_block_code τ): Continuous τ := by
  apply continuous_of_neighborhood_continuous
  intro x W hW
  obtain ⟨Ω, hΩ1, hΩ2⟩ := neighbor_lemma hW
  let ⟨S, hS1, hS2⟩ := h
  let ΩS := setMul Ω S
  exists neighbors x ΩS
  apply And.intro
  apply neighbors_is_nhd x ΩS
  apply Set.Finite.image2
  exact hΩ1
  exact hS1
  have h1: Set.image τ (neighbors x ΩS) ⊆ neighbors (τ x) Ω := by
    intro τy hτy
    simp [neighbors] at hτy
    obtain ⟨y, hy⟩ := hτy
    simp [neighbors, ←hy.2]
    exact memory_set_eq ⟨hS1, hS2⟩ hy.1
  exact le_trans h1 hΩ2


-- curtis hedlund theorem reverse direction

def funcQuot {X Y: Type} {S: Set X} (u v: X → Y) (h: Set.EqOn u v S): S → Y := sorry


lemma lemma2 {G A: Type} [TopologicalSpace A] [DiscreteTopology A] [Monoid G] {τ: (G → A) → G → A} (h1: Continuous τ):
  ∀ x: G → A, ∃ Ω: Set G, Finite Ω ∧ ∀ y: G → A, y ∈ neighbors x Ω → τ x 1 = τ y 1 := by
    let φ := proj 1 ∘ τ
    have hφ : Continuous φ := Continuous.comp (continuous_apply 1) h1
    intro x
    have hU: {φ x} ∈ nhds (φ x) := by simp
    obtain ⟨V, hV1, hV2⟩ := continuous_of_neighborhood_continuous2 hφ x {φ x} hU
    have h4 := (neighbors_forms_neighborhood_base x).2
    specialize h4 V hV1
    obtain ⟨U, hU1, hU2⟩ := h4
    simp_all
    obtain ⟨Ω, hΩ1, hΩ2⟩ := hU1
    exists Ω
    constructor
    exact hΩ1
    intro y hy
    rw [← hΩ2] at hy
    have hy2 := hU2 hy
    have hy3 := hV2
    specialize hy3 y
    have hy4 := hy3 hy2
    calc
      τ x 1 = φ x := by rfl
          _ = φ y := by rw [Eq.symm hy4]
          _ = τ y 1 := by rfl

-- lemma: suppose F: A^G → A
-- and S is a subset of F
-- suppose for all x,y ∈ A^G if x|S = y|S then F(x) = F(y)
-- then there is a unique map f: A^S → A


lemma lemma3 {φ: (G → A) → A} {S: Set G}
  (h: ∀ x y: G → A, Set.EqOn x y S → φ x = φ y):
  ∃ μ: (S → A) → A, ∀ x: G → A, φ x = μ (Set.restrict S x) := by
  sorry

theorem sliding_block_code_of_continuous_and_equivariant {G A: Type} [Group G] [Finite A] [TopologicalSpace A] [DiscreteTopology A] {τ: (G → A) → G → A}
  (h1: Continuous τ) (h2: equivariant τ): sliding_block_code τ := by

  have h3: ∃ Ω: (G → A) → Set G, ∀ x: G → A, Finite (Ω x) ∧ ∀ y: G → A, y ∈ neighbors x (Ω x) → τ x 1 = τ y 1 := by
    exists fun x => Classical.choose (lemma2 h1 x)
    intro x
    exact Classical.choose_spec (lemma2 h1 x)

  obtain ⟨Ω, hΩ⟩ := h3

  have h4 : ∀ x, Finite (Ω x) := by
    intro x
    exact (hΩ x).1

  -- the V x (Ω x) cover the whole space
  have h5 : Set.univ ⊆ ⋃ x, neighbors x (Ω x) := by
    intro x _
    simp
    exists x
    apply x_in_neighbors x

  -- extract a finite subcover
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover CompactSpace.isCompact_univ (fun x => neighbors x (Ω x)) (fun x => neighbors_open x (Ω x) (h4 x)) h5

  let S := Set.sUnion (Set.image Ω F)
  exists S

  have h6 : Finite S := by
    apply Set.Finite.sUnion
    exact Set.Finite.image Ω (by simp)
    intro _ hΩx
    simp [Set.image] at hΩx
    obtain ⟨x, hx⟩ := hΩx
    rw [←hx.2]
    exact h4 x

  apply And.intro
  exact h6

  let φ := proj 1 ∘ τ

  -- let x0 be such that y in V(x0, Ω x0)
  have h7: ∀ x: G → A, ∃ x0 ∈ F, x ∈ neighbors x0 (Ω x0) := by
    apply Set.exists_set_mem_of_union_eq_top
    apply Set.eq_univ_of_univ_subset
    -- this is almost h5
    sorry

  have h8: ∀ x y: G → A, Set.EqOn x y S → φ x = φ y := by
    intro x y h
    obtain ⟨x0, hx01, hx02⟩ := h7 x
    have h10: Ω x0 ⊆ S := by
      apply Set.subset_sUnion_of_mem
      exists x0
    have h11: y ∈ neighbors x (Ω x0) := Set.EqOn.mono h10 h
    have h12: y ∈ neighbors x0 (Ω x0) := Set.EqOn.trans hx02 h11
    have h13: τ x 1 = τ y 1 := by
      rw[←(hΩ x0).2 x hx02, (hΩ x0).2 y h12]
    exact h13

  obtain ⟨μ, hμ⟩ := lemma3 h8
  exists μ
  apply (cellular_automata_iff h6 μ).mpr
  apply And.intro
  exact h2
  intro x
  exact hμ x

-- theorem 1.8.1
theorem curtis_hedlund_lyndon {G A: Type} [Group G] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (τ: (G → A) → G → A):
  sliding_block_code τ ↔ (Continuous τ ∧ equivariant τ) := by
  apply Iff.intro
  exact fun h => ⟨sliding_block_code_continuous h, sliding_block_equivariant h⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_continuous_and_equivariant h1 h2

theorem uniform_continuous_of_sliding_block_code {G A: Type} [Group G] [UniformSpace A] {τ: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: sliding_block_code τ): UniformContinuous τ :=
  sorry

theorem sliding_block_code_of_uniform_continuous_and_equivariant {G A: Type} [Group G] [UniformSpace A] {τ: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: UniformContinuous τ) (h2:equivariant τ): sliding_block_code τ :=
  sorry

-- drops the finite assumption
theorem curtis_hedlund_lyndon_uniform {G A: Type} [Group G] [UniformSpace A] (h: uniformity A = Filter.principal idRel) (τ: (G → A) → G → A): sliding_block_code τ ↔ (UniformContinuous τ ∧ equivariant τ) := by
  apply Iff.intro
  exact fun h1 => ⟨uniform_continuous_of_sliding_block_code h h1, sliding_block_equivariant h1⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_uniform_continuous_and_equivariant h h1 h2
