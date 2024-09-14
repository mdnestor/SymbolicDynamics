/-

Results about the prodiscrete topology, defined as the product of discrete topologies

-/

import Mathlib.Topology.Bases
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
  T2Space (G → A) :=
  Pi.t2Space

theorem prodiscrete_totally_disconnected {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  TotallyDisconnectedSpace (G → A) :=
  Pi.totallyDisconnectedSpace

-- if A is finite then A^G is compact
theorem prodiscrete_compact {G A: Type} [TopologicalSpace A] [DiscreteTopology A] [Finite A]:
  CompactSpace (G → A) :=
  Pi.compactSpace

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
  simp [cylinder_open]

theorem cylinder_subset {G A: Type} (g: G) {U1: Set A} {U2: Set A} (h: U1 ⊆ U2):
  cylinder g U1 ⊆ cylinder g U2 := by
  intro _ ha
  simp_all [cylinder, proj]
  exact h ha

/-
theorem cylinder_closed {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (g: G) (U: Set A):
  IsClosed (cylinder g U) := by
  sorry

theorem cylinder_clopen {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (g: G) (U: Set A): IsClopen (cylinder g U) :=
  ⟨cylinder_closed g U, cylinder_open g U⟩
-/

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
theorem pi_generateFrom_cylinders (X I: Type) [TopologicalSpace X]:
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

-- TODO: replace with mathlib definition
def neighborhood_base {X: Type} [TopologicalSpace X] (x: X) (B: Set (Set X)): Prop :=
  B ⊆ (nhds x).sets ∧ ∀ V ∈ nhds x, ∃ U ∈ B, U ⊆ V

theorem cylinder_imply_singleton_mem {X Y: Type} {x: X} {u: X → Y} {U: Set Y}
  (h: u ∈ cylinder x U): {u x} ⊆ U := by
  simp
  exact h

theorem neighbor_singleton_subset_cylinder {X Y: Type} {x: X} {u: X → Y} {U: Set Y}
  (h: u ∈ cylinder x U): neighbors u {x} ⊆ cylinder x U := by
  rw [neighbors_cylinder_eq]
  simp
  exact cylinder_subset x (cylinder_imply_singleton_mem h)

theorem lemma0 {X Y Z: Type} {f: X → Y → Z} {S: Set Z}
  (h2: S ⊆ {z | ∃ x y, z = f x y}):
  ∃ p: S → X × Y, ∀ z: S, f (p z).1 (p z).2 = z := by
  let p: S → X × Y := by
    intro ⟨s, hs⟩
    have h3 := h2 hs
    simp at h3
    let x := Classical.choose h3
    let h4 := Classical.choose_spec h3
    let y := Classical.choose h4
    exact (x, y)
  exists p
  simp
  intro z hz
  have h3 := h2 hz
  simp at h3
  let h4 := Classical.choose_spec h3
  let h5 := Classical.choose_spec h4
  rw [← h5]

theorem lemma1 {X Y Z: Type} {f: X → Y → Z} {S: Set Z}
  (h2: S ⊆ {z | ∃ x y, z = f x y}):
  ∃ p1: S → X, ∃ p2: S → Y, ∀ z: S, f (p1 z) (p2 z) = z := by
  obtain ⟨p, hp⟩ := lemma0 h2
  exists fun z => (p z).1
  exists fun z => (p z).2

theorem lemma2 {A B C: Type} {f: A → B → Set C} {X: Set (Set C)} (h1: Finite X) (h2: X ⊆ {C | ∃ x y, C = f x y}):
  ∃ p: Set (A × B), p.Finite ∧ X = Set.image (fun (x, y) => f x y) p := by
  have h1 : ∃ pick_x : X → A, ∃ pick_y : X → B,
    ∀ c : X, f (pick_x c) (pick_y c) = c := lemma1 h2
  obtain ⟨ pick_x, pick_y, hpick⟩ := h1
  exists Set.image (fun x => (pick_x x, pick_y x)) Set.univ
  constructor
  . apply Set.Finite.image
    apply Set.finite_univ
  . simp_all
    ext
    simp_all
    apply Iff.intro
    · intro a
      constructor
      · constructor
        · constructor
          constructor
          constructor
          · constructor
            · rfl
            · rfl
          on_goal 3 => {
            simp_all
            rfl
          }
          · simp_all
    · intro a
      obtain ⟨_, h⟩ := a
      obtain ⟨_, h⟩ := h
      obtain ⟨left, right1⟩ := h
      obtain ⟨_, h⟩ := left
      obtain ⟨_, h⟩ := h
      obtain ⟨left, right2⟩ := h
      subst left right1 right2
      simp_all only

/-
V(x, Ω) forms a neighborhood basis for x

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
    have h1 := TopologicalSpace.isTopologicalBasis_of_subbasis (pi_generateFrom_cylinders A G)
    obtain ⟨B, hB1, hB2, hB3⟩ := (TopologicalSpace.IsTopologicalBasis.mem_nhds_iff h1).mp hV
    obtain ⟨Cs, hCs⟩ := hB1
    simp at hCs
    have h2: ∃ params: Set (G × Set A), params.Finite ∧ Cs = Set.image (fun (gi, Ui) => cylinder gi Ui) params := lemma2 hCs.1.1 hCs.1.2
    obtain ⟨params, hparams⟩ := h2
    let Ω := Set.image (fun p => p.1) params
    exists Set.sInter (Set.image (fun g => cylinder g {x g}) Ω)
    simp
    constructor
    exists Ω
    constructor
    exact Set.Finite.image (fun p => p.1) hparams.1
    simp [neighbors_cylinder_eq]
    have h3: ∀ p ∈ params, cylinder p.1 {x p.1} ⊆ cylinder p.1 p.2 := by
      intro p hp
      apply cylinder_subset
      apply cylinder_imply_singleton_mem
      simp_all
      obtain ⟨_, right1⟩ := hCs
      obtain ⟨_, right2⟩ := hparams
      subst right1 right2
      simp_all
    have h4: ⋂ p ∈ params, cylinder p.1 p.2 = ⋂₀ Cs := by simp_all
    calc
      ⋂ g ∈ Ω, cylinder g {x g} = ⋂ p ∈ params, cylinder p.1 {x p.1} := by exact Set.biInter_image
                              _ ⊆ ⋂ p ∈ params, cylinder p.1 p.2 := by apply Set.iInter₂_mono; exact h3
                              _ = ⋂₀ Cs := h4
                              _ = B := hCs.2
                              _ ⊆ V := hB3

-- "Let x: G → A and let W be a neighborhood of τ(x). Then we can find a finite subset Ω ⊆ G such that V(τ(x), Ω) ⊆ W" why..?
theorem neighbor_lemma {G A: Type} [TopologicalSpace A] [DiscreteTopology A]
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
