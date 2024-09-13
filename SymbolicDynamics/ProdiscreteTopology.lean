/-

Results about the prodiscrete topology, defined as the product of discrete topologies

-/

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Separation
import Mathlib.Topology.Connected.TotallyDisconnected

-- the prodiscrete topology is the product of discrete spaces via the Π construction
def product_space (G A: Type) [TopologicalSpace A]: TopologicalSpace (G → A) :=
  Pi.topologicalSpace

def prodiscrete_space (G A: Type) [TopologicalSpace A] [DiscreteTopology A]: TopologicalSpace (G → A) :=
  product_space G A

-- it is both T2 (Hausdorff) and totally disconnected
theorem prodiscrete_T2 {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  T2Space (G → A) := by
  apply Pi.t2Space

theorem prodiscrete_totally_disconnected {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  TotallyDisconnectedSpace (G → A) := by
  apply Pi.totallyDisconnectedSpace

-- if A is finite then A^G is compact
theorem prodiscrete_compact {G A: Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]:
  CompactSpace (G → A) := by
  apply Pi.compactSpace

-- projection map
def proj {G A: Type} (g: G): (G → A) → A :=
  fun x: G → A => x g

def cylinder {G A: Type} (g: G) (U: Set A): Set (G → A) :=
  Set.preimage (proj g) U

theorem elt_cylinder_eq {G A: Type} (g: G) (a: A):
  cylinder g {a} = {x: G → A | x g = a} := rfl

theorem cylinder_open {G A: Type} [TopologicalSpace A] (g: G) {U: Set A} (h: IsOpen U):
  IsOpen (cylinder g U) := by
  apply Continuous.isOpen_preimage
  exact continuous_apply g
  exact h

-- every cylinder in the prodiscrete topology is open
theorem prodiscrete_cylinder_open {G A: Type} [TopologicalSpace A] [DiscreteTopology A]
  (g: G) (U: Set A): IsOpen (cylinder g U) := by
  apply cylinder_open
  simp

theorem cylinder_subset {G A: Type} (g: G) {U1: Set A} {U2: Set A} (h: U1 ⊆ U2):
  cylinder g U1 ⊆ cylinder g U2 := by
  intro _ ha
  simp_all [cylinder, proj]
  exact h ha

/-
theorem cylinder_closed {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (g: G) (a: A):
  IsClosed (cylinder g {a}) := by
  sorry
-/

/-
theorem cylinder_clopen {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (g: G) (a: A): IsClopen (cylinder g {a}) :=
  ⟨cylinder_closed g {a}, cylinder_open g {a}⟩
-/

-- a set is open iff. it is a union of finite intersections of cylinders
-- is this just isOpen_pi_iff?

-- a set U is a finite intersection of cylinders
-- if there exists a finite type I and maps g: I → G and a: I → Set G
-- such that U is the intersection of cylinder (g i) (a i) for i ∈ I

-- the prodiscrete topology is generated by cylinders
-- think I need to use pi_eq_generateFrom

/-
theorem continuous_iff_preimage_basic_open {X Y: Type} [TopologicalSpace X] [T: TopologicalSpace Y]
  {S: Set (Set Y)} (hT: T = TopologicalSpace.generateFrom S) (f: X → Y):
  Continuous f ↔ ∀ U ∈ S, IsOpen (Set.preimage f U) := by
  apply Iff.intro
  intro h V hV
  sorry
  -- apply continuous_generateFrom_iff.mpr
  /- tactic 'apply' failed, failed to unify
  @Continuous ?m.1795 ?m.1796 ?m.1798 (TopologicalSpace.generateFrom ?m.1799) ?m.1797
with
  @Continuous X Y inst✝ T f -/
  sorry
-/

def finite_intersection_of_cylinders {A G: Type} (U: Set (G → A)): Prop :=
  ∃ I: Type, ∃ g: I → G, ∃ a: I → Set A,
  Finite I ∧ U = Set.sInter (Set.image (fun i => cylinder (g i) (a i)) Set.univ)

-- the set of cylinders
@[simp]
def cylinders (X I: Type) [TopologicalSpace X]: Set (Set (I → X)) :=
  {C: Set (I → X) | ∃ i: I, ∃ U: Set X, IsOpen U ∧ C = cylinder i U}

-- the set of "square cylinders"
@[simp]
def square_cylinders (X I: Type) [TopologicalSpace X]: Set (Set (I → X)) :=
  {C | ∃ U: I → Set X, ∃ ι: Finset I, (∀ i ∈ ι, IsOpen (U i)) ∧ C = (Finset.toSet ι).pi U}

-- every square cylinder is a finite intersection of cylinders
theorem square_cylinders_are_finite_intersections_of_cylinders {X I: Type} [TopologicalSpace X]
  {S: Set (I → X)} (h: S ∈ square_cylinders X I):
  ∃ ι: Finset I, ∃ U: ι → Set X, (∀ i: ι, IsOpen (U i)) ∧ S = Set.iInter (fun i: ι => cylinder (↑i) (U i)) := by
  obtain ⟨U, ι, h1, h2⟩ := h
  exists ι, Set.restrict ι U
  apply And.intro
  intro i
  apply h1 i
  simp
  rw [h2]
  ext
  simp [Set.mem_iInter]
  rfl

-- the product topology is coarser than the topology generated by cylinders
theorem pi_le_generateFrom_cylinders {X I: Type} [TopologicalSpace X]:
  Pi.topologicalSpace ≤ TopologicalSpace.generateFrom (cylinders X I) := by
  apply le_generateFrom
  simp
  intro _ i _ hU hC
  rw [hC]
  exact cylinder_open i hU

-- the topology generated by cylinders is coarser than the product topology
 theorem generateFrom_cylinders_le_pi {X I: Type} [TopologicalSpace X]:
  TopologicalSpace.generateFrom (cylinders X I) ≤ Pi.topologicalSpace := by
  rw [pi_eq_generateFrom, cylinders]
  apply le_generateFrom
  intro S hS
  obtain ⟨ι, U, h1, h2⟩ := square_cylinders_are_finite_intersections_of_cylinders hS
  rw [h2]
  apply @isOpen_iInter_of_finite (I → X) ι (TopologicalSpace.generateFrom (cylinders X I))
  intro i
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exists i, U i
  constructor
  apply h1 i
  rfl

-- the product space is generated by cylinders
theorem pi_generateFrom_cylinders {X I: Type} [TopologicalSpace X]:
  Pi.topologicalSpace = TopologicalSpace.generateFrom (cylinders X I) :=
  le_antisymm pi_le_generateFrom_cylinders generateFrom_cylinders_le_pi

-- neighborhood definition of continuity
theorem continuous_of_neighborhood_continuous {X Y: Type} [TopologicalSpace X] [TopologicalSpace Y] {f: X → Y}:
  Continuous f ↔ (∀ x: X, ∀ V ∈ nhds (f x), ∃ U ∈ nhds x, Set.image f U ⊆ V) := by
  constructor
  intro h x V hV
  exists Set.preimage f V
  constructor
  rw [continuous_iff_continuousAt] at h
  specialize h x
  exact h hV
  simp
  intro h
  apply continuous_iff_continuousAt.mpr
  intro x V hV
  specialize h x V hV
  obtain ⟨U, hU1, hU2⟩ := h
  simp
  simp at hU2
  exact Filter.mem_of_superset hU1 hU2

-- neighbor set (same as V(x, Ω), eq 1.3)
-- given x: G → A and Ω ⊆ G, the Ω-neighbors of x will be
-- all those y which agree with x on Ω
def neighbors {G A: Type} (x: G → A) (Ω: Set G): Set (G → A) :=
  {y: G → A | Set.EqOn x y Ω}

-- if Ω1 ⊆ Ω2 then neighbors(x, Ω1) ⊇ neighbors(x, Ω2)
theorem neighbors_incl {G A: Type} (x: G → A) {Ω1: Set G} {Ω2: Set G} (h: Ω1 ⊆ Ω2): neighbors x Ω2 ⊆ neighbors x Ω1 :=
  fun _ hy _ hg => hy (h hg)

-- neighbors(x, G) = {x}
theorem neighbors_univ {G A: Type} (x: G → A): neighbors x Set.univ = {x} := by
  simp [neighbors]

-- neighbors(x, ∅) = G → A
theorem neighbors_empty {G A: Type} (x: G → A): neighbors x ∅ = Set.univ := by
  simp [neighbors]

-- x ∈ neighbors(x, Ω)
theorem x_in_neighbors {G A: Type} (x: G → A) (Ω: Set G): x ∈ neighbors x Ω := by
  simp [neighbors, Set.EqOn]

-- neighbors(x, Ω) is equal to the intersection of all cylinders of the form C(g, x(g)) for g ∈ Ω
theorem neighbors_cylinder_eq {G A: Type} (x: G → A) (Ω: Set G):
  neighbors x Ω = Set.sInter (Set.image (fun g => cylinder g {x g}) Ω) := by
  simp [cylinder, neighbors, Set.EqOn]
  ext
  rw [Set.mem_setOf_eq, Set.mem_iInter]
  apply Iff.intro
  · intros
    simp_all [proj]
  · intros
    simp_all [proj]

theorem neighbors_open {G A: Type} [TopologicalSpace A] [DiscreteTopology A]
  (x: G → A) (Ω: Set G) (h: Finite Ω): IsOpen (neighbors x Ω) := by
  rw [neighbors_cylinder_eq]
  apply Set.Finite.isOpen_sInter
  apply Set.Finite.image
  exact h
  intro U
  simp
  intro _ _ hU
  rw [←hU]
  apply cylinder_open
  simp

theorem neighbors_is_nhd {G A: Type} [TopologicalSpace A] [DiscreteTopology A]
  (x: G → A) (Ω: Set G) (h: Finite Ω):
  neighbors x Ω ∈ nhds x := by
  exact IsOpen.mem_nhds (neighbors_open x Ω h) (x_in_neighbors x Ω)


def neighborhood_base {X: Type} [TopologicalSpace X] (x: X) (B: Set (Set X)): Prop :=
  B ⊆ (nhds x).sets ∧ ∀ V ∈ nhds x, ∃ U ∈ B, U ⊆ V

-- if a topology is generated from B then every open set contains a basic subset
theorem open_basic_subset {X: Type} [T: TopologicalSpace X] {B: Set (Set X)}
  (h: T = TopologicalSpace.generateFrom B) {U: Set X} (hU: IsOpen U):
  ∃ b ∈ B, b ⊆ U := by
  sorry

-- every open set contains a finite intersection of cylinders
theorem open_contains_finite_cylinders {X: Type} [T: TopologicalSpace X]
  {B: Set (Set X)}
  (h: T = TopologicalSpace.generateFrom B) {U: Set X} (h: IsOpen U):
  ∃ I: Type, ∃ V: I → Set X, Finite I ∧ (∀ i: I, V i ∈ B) ∧ Set.iInter V ⊆ U := by
  sorry

theorem cylinder_imply_singleton_mem {X Y: Type} [TopologicalSpace X] {x: X} {u: X → Y} {U: Set Y}
  (h: u ∈ cylinder x U): {u x} ⊆ U := by
  simp
  exact h

theorem neighbor_singleton_subset_cylinder {X Y: Type} [TopologicalSpace X] {x: X} {u: X → Y} {U: Set Y}
  (h: u ∈ cylinder x U): neighbors u {x} ⊆ cylinder x U := by
  rw [neighbors_cylinder_eq]
  simp
  exact cylinder_subset x (cylinder_imply_singleton_mem h)

/-
Proof idea:

1. show for all x and Ω finite, V(x,Ω) ∈ nhds x

2. show for every neighborhood N of x, there exists a finite set Ω such that V(x, Ω) ⊆ N

-- every neighborhod of x contains a basic open set B containing x
-- every basic open set is a finite intersection of generating sets
-- generating sets are cylinders so we have x ∈ B = ∩_{i=1}^{n} C(g_i, U_i) where each U_i is open
-- let Ω := {g_i | i = 1, ..., n}
-- note that x ∈ C(g_i, U_i) for all i
-- from `cylinder_imply_singleton_mem` it follows that {x g_i} ⊆ U_i
-- from `cylinder_subset` it follows that C(g_i, {x g_i}) ⊆ C(g_i, U_i)
-- then:
-- V(x, Ω) = ∩_{i=1}^{n} C(g_i, x g_i)      by `neighbors_cylinder_eq`
           ⊆ ∩_{i=1}^{n} C(g_i, U_i)        by `cylinder_subset`
           = B
           ⊆ N
-/
theorem neighbors_forms_neighborhood_base {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (x: G → A):
  neighborhood_base x {U: Set (G → A) | ∃ Ω: Set G, Finite Ω ∧ U = neighbors x Ω } := by
  constructor
  . intro U hU
    simp_all
    obtain ⟨Ω, hΩ1, hΩ2⟩ := hU
    rw [hΩ2]
    exact neighbors_is_nhd x Ω hΩ1
  . intro V hV
    simp
    have h1: ∀ x' ∈ (Set.singleton x), V ∈ nhds x' := by
      intro _ hx
      rw [Set.eq_of_mem_singleton hx]
      exact hV
    obtain ⟨U, hU1, hU2, hU3⟩ := exists_open_set_nhds h1
    -- every open set contains a basic set?
    obtain ⟨I, W, hW1, hW2, hW3⟩ := open_contains_finite_cylinders pi_generateFrom_cylinders hU2
    exists Set.iInter W
    constructor
    have s:= fun i: I => Classical.choose (hW2 i)

    exists Set.image s Set.univ

    constructor
    sorry

    simp_all [cylinders]
    ext u
    constructor
    intro hu
    simp at hu

    sorry
    sorry
    exact le_trans hW3 hU3

-- "Let x: G → A and let W be a neighborhood of τ(x). Then we can find a finite subset Ω ⊆ G such that V(τ(x), Ω) ⊆ W" why..?
theorem neighbor_lemma {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A]
  {W: Set (G → A)} {x: G → A} (h2: W ∈ nhds x):
  ∃ Ω: Set G, Finite Ω ∧ neighbors x Ω ⊆ W := by
  have h3 := neighbors_forms_neighborhood_base x
  simp [neighborhood_base] at h3
  obtain ⟨U, hU⟩ := h3.2 W h2
  obtain ⟨Ω, hΩ⟩ := hU.1
  exists Ω
  constructor
  exact hΩ.1
  rw [←hΩ.2]
  exact hU.2
