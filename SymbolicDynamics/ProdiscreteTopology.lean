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

-- definition of sliding block code based on definition 1.4.1

-- results about the prodiscrete topology

-- it is both T2 (Hausdorff) and totally disconnected

theorem prodiscrete_T2 {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  T2Space (G → A) := by
  apply Pi.t2Space

theorem prodiscrete_totally_disconnected {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  TotallyDisconnectedSpace (G → A) := by
  apply Pi.totallyDisconnectedSpace

-- projection map
def proj {G A: Type} (g: G): (G → A) → A :=
  fun x: G → A => x g

-- every projection map is continuous in prodiscrete topology
-- this is the theorem continuous_apply


-- the shift map is continuous
theorem shift_continuous {A M: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]:
  ∀ g: M, Continuous (fun x: M → A => x ∘ leftMul g) := by
    sorry

theorem shift_uniform_continuous {A M: Type} [Mul M] [UniformSpace A] (h: uniformity A = Filter.principal idRel):
  ∀ g: M, UniformContinuous (fun x: M → A => x ∘ leftMul g) := by
    sorry

def cylinder {G A: Type} (g: G) (U: Set A): Set (G → A) :=
  Set.preimage (proj g) U

def elt_cylinder {G A: Type} (g: G) (a: A): Set (G → A) :=
  cylinder g {a}

theorem elt_cylinder_eq {G A: Type} (g: G) (a: A):
  elt_cylinder g a = {x: G → A | x g = a} := rfl

theorem cylinder_open {G A: Type} [TopologicalSpace A] (g: G) {U: Set A} (h: IsOpen U):
  IsOpen (cylinder g U) := by
  apply Continuous.isOpen_preimage
  exact continuous_apply g
  exact h

-- every
theorem prodiscrete_cylinder_open {G A: Type} [TopologicalSpace A] [DiscreteTopology A]
  (g: G) (U: Set A): IsOpen (cylinder g U) := by
  apply cylinder_open
  simp

theorem elt_cylinder_open {G A: Type} [TopologicalSpace A] [DiscreteTopology A]
  (g: G) (a: A): IsOpen (elt_cylinder g a) := by
  apply prodiscrete_cylinder_open

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
