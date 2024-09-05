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
def prodiscrete {G A: Type} [TopologicalSpace A] [DiscreteTopology A]: TopologicalSpace (G → A) :=
  Pi.topologicalSpace

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

theorem cylinder_closed {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (g: G) (a: A):
  IsClosed (cylinder g {a}) := by
  sorry

/--/
theorem cylinder_clopen {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (g: G) (a: A): IsClopen (cylinder g {a}) :=
  ⟨cylinder_closed g {a}, cylinder_open g {a}⟩
-/

-- a set is open iff. it is a union of finite intersections of cylinders
-- is this just isOpen_pi_iff?

-- a set U is a finite intersection of cylinders
-- if there exists a finite type I and maps g: I → G and a: I → Set G
-- such that U is the intersection of cylinder (g i) (a i) for i ∈ I
def finite_intersection_of_cylinders {A G: Type} (U: Set (G → A)): Prop :=
  ∃ I: Type, ∃ g: I → G, ∃ a: I → Set A,
  Finite I ∧ U = Set.sInter (Set.image (fun i => cylinder (g i) (a i)) Set.univ)

-- a finite intersection of arbitrary cylinders is open in the discrete topology
theorem finite_intersection_of_cylinders_open {A G: Type}
  [TopologicalSpace A] [DiscreteTopology A] {U: Set (G → A)}
  (h: finite_intersection_of_cylinders U): IsOpen U := by
  obtain ⟨_, _, _, _, h2⟩ := h
  simp [h2]
  apply isOpen_iInter_of_finite
  intro
  apply prodiscrete_cylinder_open

-- a union of finite intersections of cylinders
def union_of_finite_inter_of_cylinders {A G: Type}
  (U: Set (G → A)): Prop :=
  ∃ UU: Set (Set (G → A)), Set.sUnion UU = U ∧
    ∀ V ∈ UU, finite_intersection_of_cylinders V

-- a union of finite intersections of cylinders is open
theorem open_of_union_of_finite_intersection_of_cylinders
  {A G: Type} [TopologicalSpace A] [DiscreteTopology A] {U: Set (G → A)}
  (h: union_of_finite_inter_of_cylinders U): IsOpen U := by
  obtain ⟨UU, hUU1, hUU2⟩ := h
  rw [← hUU1]
  apply isOpen_sUnion
  intro V hV
  apply finite_intersection_of_cylinders_open
  apply hUU2
  exact hV

-- every open set is a union of finite intersections of open cylinders
-- I think this has to do with them forming a basis
theorem union_of_finite_intersection_of_cylinders_of_open
  {A G: Type} [TopologicalSpace A] [DiscreteTopology A] {U: Set (G → A)}
  (h: IsOpen U): union_of_finite_inter_of_cylinders U := by
  sorry

theorem open_iff_union_of_finite_intersection_of_cylinders
  {A G: Type} [TopologicalSpace A] [DiscreteTopology A] {U: Set (G → A)}:
  IsOpen U ↔ union_of_finite_inter_of_cylinders U :=
  ⟨
    union_of_finite_intersection_of_cylinders_of_open,
    open_of_union_of_finite_intersection_of_cylinders
  ⟩

-- neighborhood definition of continuity
-- TODO find in mathlib
lemma continuous_of_neighborhood_continuous {X Y: Type} [TopologicalSpace X] [TopologicalSpace Y] {f: X → Y} (h: ∀ x: X, ∀ V ∈ nhds (f x), ∃ U ∈ nhds x, Set.image f U ⊆ V): Continuous f := by
  sorry

lemma continuous_of_neighborhood_continuous2 {X Y: Type} [TopologicalSpace X] [TopologicalSpace Y] {f: X → Y} (h: Continuous f): ∀ x: X, ∀ V ∈ nhds (f x), ∃ U ∈ nhds x, Set.image f U ⊆ V := by
  sorry
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
    -- ⊢ ∃ U, (∃ Ω, Finite ↑Ω ∧ U = _root_.V x Ω) ∧ U ⊆ V
    sorry

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
