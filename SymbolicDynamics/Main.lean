/-

Main reults:

-- defines the shift map and proves it is continuous
-- defines sliding block code
-- proves the Curtis–Hedlund–Lyndon (CHL) theorem
-- defines subshifts

TODO:

-- variant of CHL theorem for subshifts
-- CHL theorem for uniform structures
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

-- results about the shift map
def shift {M A: Type} [Mul M] (g: M): (M → A) → (M → A) :=
  fun x => x ∘ leftMul g

theorem shift_comp {M A: Type} [Semigroup M] {x: M → A} {g1 g2: M}: shift g1 (shift g2 x) = shift (g2 * g1) x := by
  ext
  simp [shift, leftMul, mul_assoc]

theorem shift_one {T X: Type} {u: T → X} [Monoid T]: shift 1 u = u := by
  ext
  simp [shift, leftMul]

theorem shift_preimage_cylinder_eq {G A: Type} [Mul G] (g g': G) (S: Set A):
  Set.preimage (shift g) (cylinder g' S) = cylinder (g * g') S := by
  rfl

theorem shift_continuous {M A: Type} [Mul M] (g: M) [TopologicalSpace A] [DiscreteTopology A]:
  Continuous[Pi.topologicalSpace, Pi.topologicalSpace] (fun x: M → A => shift g x) := by
  rw [pi_generateFrom_cylinders]
  apply continuous_generateFrom_iff.mpr
  intro V
  simp
  intro x U hV
  rw [hV, shift_preimage_cylinder_eq]
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  simp

-- F is equivariant if it commutes with the shift
def equivariant {T X Y: Type} [Mul T] (F: (T → X) → T → Y): Prop :=
  ∀ u: T → X, ∀ t: T, F (shift t u) = shift t (F u)

theorem shift_one_equivariant {T X Y: Type} [Monoid T] {F: (T → X) → T → Y} {x: T → X} {t: T}
  (hf: equivariant F): F x t = F (shift t x) 1 := by
  calc
    F x t = F x (t * 1) := by rw [mul_one]
        _ = ((F x) ∘ (leftMul t)) 1 := by rfl
        _ = (shift t (F x)) 1 := by rfl
  rw [hf]

def local_map {A B T: Type} [Mul T] {S: Set T} (F: (T → A) → T → B) (f: (S → A) → B): Prop :=
  ∀ x: T → A, ∀ t: T, F x t = f (Set.restrict S (shift t x))

-- if F has a local map then it is equivariant
theorem local_map_equivariant {A B T: Type} [Semigroup T] {S: Set T} {F: (T → A) → T → B} {f: (S → A) → B}
  (h: local_map F f): equivariant F := by
  intro u t
  ext t'
  rw [h (shift t u) t']
  --rw [shift_comp]

  repeat simp [shift]
  rw [h]
  congr
  rw [Set.restrict_eq_restrict_iff]
  apply Set.EqOn.mono (Set.subset_univ S)
  apply (Set.eqOn_univ ((u ∘ leftMul t) ∘ leftMul t') (shift (leftMul t t') u)).mpr
  ext
  simp [shift, leftMul]
  rw [mul_assoc]

def memory_set {T X Y: Type} [Mul T] (F: (T → X) → T → Y) (S: Set T): Prop :=
  ∃ f: (S → X) → Y, local_map F f

-- if F is equivariant and T is a monoid then the universe is a memory set
def memory_set_univ {T X Y: Type} [Monoid T] {F: (T → X) → T → Y}
  (hf: equivariant F): memory_set F Set.univ := by
  exists fun x => F (x ∘ (@Equiv.Set.univ T).invFun) 1
  intro _ _
  rw [shift_one_equivariant hf]
  congr

-- if T is a monoid then {1} is a memory set for the identity on T → X
def memory_set_id {T X: Type} [Monoid T]: memory_set (@id (T → X)) {1} := by
  exists fun x => x ⟨1, rfl⟩
  intro
  simp [leftMul, shift]

-- memory sets are upward closed
def memory_set_incl {T X Y: Type} [Mul T] {F: (T → X) → T → Y} {S1 S2: Set T} (h1: memory_set F S1) (h2: S1 ⊆ S2): memory_set F S2 := by
  obtain ⟨f1, hf1⟩ := h1
  exists fun x => f1 (fun ⟨a, ha⟩ => x ⟨a, h2 ha⟩)

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

-- definition of sliding block code: there exists a finite memory set
-- todo: generalize to shift spaces besides the full shit spaces
def sliding_block_code {T X Y: Type} [Mul T] (F: (T → X) → T → Y): Prop :=
  ∃ S: Set T, Finite S ∧ memory_set F S

theorem equivariant_compose {T X Y Z: Type} [Mul T] {F1: (T → X) → T → Y} {F2: (T → Y) → T → Z} (h1: equivariant F1) (h2: equivariant F2): equivariant (F2 ∘ F1) := by
  simp [equivariant]
  intros
  rw [h1, h2]

theorem sliding_block_equivariant {T X Y: Type} [Semigroup T] {F: (T → X) → T → Y} (h: sliding_block_code F): equivariant F := by
  obtain ⟨_, _, hS2⟩ := h
  obtain ⟨_, hf⟩ := hS2
  exact local_map_equivariant hf

lemma eval_at_one {T X Y: Type} [Monoid T] {F: (T → X) → T → Y}
  (u: T → X) (t: T) (h: equivariant F): F u t = F (shift t u) 1 := by
  rw [h]
  simp [shift, leftMul]

-- f is a local map for F iff. F is equivariant and ∀ x, F(x)(1) = f (x|S)
theorem local_map_iff {T X Y: Type} [Monoid T]
  {F: (T → X) → T → Y} {S: Set T} (hS: Finite S) (f: (S → X) → Y):
  local_map F f ↔ equivariant F ∧ ∀ u, F u 1 = f (S.restrict u) := by
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
theorem memory_set_compose {G A B C: Type} [Mul G]
  {F1: (G → A) → G → B} {F2: (G → B) → G → C}
  {S1 S2: Set G} (h1: memory_set F1 S1) (h2: memory_set F2 S2):
  memory_set (F2 ∘ F1) (setMul S1 S2) := by
    obtain ⟨f1, hf1⟩ := h1
    obtain ⟨f2, hf2⟩ := h2
    -- need a map from ((S1*S2) → A) → C
    sorry

-- every sliding block code is continuous
theorem sliding_block_code_continuous {T X Y: Type} [Monoid T] [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y]
  {F: (T → X) → T → Y} (h: sliding_block_code F): Continuous F := by
  apply continuous_of_neighborhood_continuous.mpr
  intro u V hV
  obtain ⟨Ω, hΩ1, hΩ2⟩ := exists_finite_eqOn_nhd hV
  let ⟨S, hS1, hS2⟩ := h
  let ΩS := setMul Ω S
  exists eqOn_nhd u ΩS
  apply And.intro
  apply eqOn_nhd_is_nhd u ΩS
  apply Set.Finite.image2
  exact hΩ1
  exact hS1
  have h1: Set.image F (eqOn_nhd u ΩS) ⊆ eqOn_nhd (F u) Ω := by
    intro Fy hFy
    simp [eqOn_nhd] at hFy
    obtain ⟨v, hv1, hv2⟩ := hFy
    simp [eqOn_nhd, ←hv2]
    exact memory_set_eq hS2 hv1
  exact le_trans h1 hΩ2

-- helper lemmas
theorem exists_neighbor_eqAt_one {T X Y: Type} [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y] [Monoid T] {F: (T → X) → T → Y} (h: Continuous F):
  ∀ u: T → X, ∃ Ω: Set T, Finite Ω ∧ ∀ v: T → X, v ∈ eqOn_nhd u Ω → F u 1 = F v 1 := by
    let φ := proj 1 ∘ F
    have hφ : Continuous φ := Continuous.comp (continuous_apply 1) h
    intro u
    have hU: {φ u} ∈ nhds (φ u) := by simp
    obtain ⟨V, hV1, hV2⟩ := continuous_of_neighborhood_continuous.mp hφ u {φ u} hU
    have h4 := (eqOn_nhd_forms_neighborhood_base u).right
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

-- if X is nonempty and finite and F: (T → X) → T → Y is continuous and equivariant then it is a sliding block
theorem sliding_block_code_of_continuous_and_equivariant {T X Y: Type} [Monoid T] [Finite X] [Nonempty X] [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y] {F: (T → X) → T → Y} (h1: Continuous F) (h2: equivariant F): sliding_block_code F := by
  have h3: ∃ Ω: (T → X) → Set T, ∀ u: T → X, Finite (Ω u) ∧ ∀ v: T → X, v ∈ eqOn_nhd u (Ω u) → F u 1 = F v 1 := by
    exists fun u => Classical.choose (exists_neighbor_eqAt_one h1 u)
    exact fun u => Classical.choose_spec (exists_neighbor_eqAt_one h1 u)
  obtain ⟨Ω, hΩ⟩ := h3
  have h4 : ∀ u, Finite (Ω u) := fun u => (hΩ u).left
  have h5 : Set.univ ⊆ ⋃ u, eqOn_nhd u (Ω u) := by
    intro u _
    simp
    exists u
    apply eqOn_nhd_self u
  obtain ⟨C, hC⟩ := IsCompact.elim_finite_subcover CompactSpace.isCompact_univ (fun u => eqOn_nhd u (Ω u)) (fun u => eqOn_nhd_open u (Ω u) (h4 u)) h5
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
    exact h4 x
  constructor
  exact hS
  have h7: ∀ x: T → X, ∃ x0 ∈ C, x ∈ eqOn_nhd x0 (Ω x0) := by
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
    obtain ⟨x0, hx0⟩ := h7 x
    simp [proj, ←(hΩ x0).right x hx0.right, (hΩ x0).2 y (Set.EqOn.trans hx0.right (Set.EqOn.mono (h8 x0 hx0.left) h))]
  obtain ⟨f, hf⟩ := exists_local_map h9
  exists f
  apply (local_map_iff hS f).mpr
  exact ⟨h2, hf⟩

/-
Curtis-Hedlund-Lyndon theorem:
If A is finite then a map F: (G → A) → (G → A) is a sliding block code iff. it is both equivariant and continuous
-/
theorem curtis_hedlund_lyndon {G A: Type} [Monoid G] [Finite A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (F: (G → A) → G → B): sliding_block_code F ↔ (Continuous F ∧ equivariant F) :=
  ⟨fun h => ⟨sliding_block_code_continuous h, sliding_block_equivariant h⟩, fun ⟨h1, h2⟩ => sliding_block_code_of_continuous_and_equivariant h1 h2⟩

-- uniform space
instance {G A: Type} [UniformSpace A]:
  UniformSpace (G → A) :=
  Pi.uniformSpace (fun _ => A)

instance {G A: Type} [UniformSpace A] (h: uniformity A = Filter.principal idRel):
  uniformity (G → A) = Filter.principal idRel := by
  sorry


theorem uniform_continuous_of_sliding_block_code {G A: Type} [Group G] [UniformSpace A] {F: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: sliding_block_code F): UniformContinuous F :=
  sorry

theorem sliding_block_code_of_uniform_continuous_and_equivariant {G A: Type} [Group G] [UniformSpace A] {F: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: UniformContinuous F) (h2:equivariant F): sliding_block_code F := by
  sorry

-- drops the finite assumption
theorem curtis_hedlund_lyndon_uniform {G A: Type} [Group G] [UniformSpace A] (h: uniformity A = Filter.principal idRel) (F: (G → A) → G → A): sliding_block_code F ↔ (UniformContinuous F ∧ equivariant F) := by
  apply Iff.intro
  exact fun h1 => ⟨uniform_continuous_of_sliding_block_code h h1, sliding_block_equivariant h1⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_uniform_continuous_and_equivariant h h1 h2

class Subshift {M A: Type} [Mul M] [TopologicalSpace A] (S: Set (M → A)): Prop where
  closed: IsClosed S
  shift_invariant: ∀ x ∈ S, ∀ g: M, shift g x ∈ S

export Subshift (closed shift_invariant)

theorem Subshift_empty {M A: Type} [Mul M] [TopologicalSpace A]:
  Subshift (∅: Set (M → A)) := by
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
  sorry
  /-
  rw [hF2]
  exact shift_invariant (F x) hx g
  -/

-- the image of a subshift under a sliding block is a subshift
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
  sorry
  -- rw [hF2, hy2]
