
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

--import SymbolicDynamics.ProdiscreteTopology

-- `Block X Y` is defined as the Sigma type of dependent pairs (Ω, f) where Ω: Set X and f: Ω → Y.
-- They are a pretty neat data strucure so they get their own file.

variable {X Y: Type*}

def Block (X: Type u1) (Y: Type u2): Type (max u1 u2) := Σ (S: Set X), S → Y

-- the empty function
def empty_func: (@∅: Set X) → Y :=
  fun ⟨x, hx⟩ => False.elim ((Set.mem_empty_iff_false x).mp hx)

-- the empty block between two types
def Block_empty (X Y: Type*): Block X Y := ⟨∅, empty_func⟩

-- given a map u: X → Y and a subset Ω ⊆ X, this is the induced block (Ω, u|Ω)
def Block_induced (u: X → Y) (Ω: Set X): Block X Y :=
  ⟨Ω, Ω.restrict u⟩

-- given a function u: X → Y, the corresponding universal block
def Block_univ (u: X → Y): Block X Y := Block_induced u Set.univ

-- (Ω, u|Ω) = (Ω, v|Ω) iff u|Ω = v|Ω
def Block_induced_eqon_iff (u v: X → Y) (Ω: Set X):
  Block_induced u Ω = Block_induced v Ω ↔ Set.EqOn u v Ω := by
  simp [Block_induced]
  simp [Set.EqOn]
  constructor
  intro h x hx
  sorry
  intro h
  sorry

-- A block b = (Ω, f) `appears` in a function u: X → Y if u|Ω = f.
def appears {X Y: Type*} (u: X → Y) (b: Block X Y): Prop :=
  Set.restrict b.fst u = b.snd

def appears_iff {X Y: Type*} (u: X → Y) (b: Block X Y): appears u b ↔ Block_induced u b.1 = b := by
  simp_all [appears, Block_induced]
  constructor
  simp_all
  intro h
  rw [←h]

-- if S1 ⊆ S2 and f: S2 → Y this is the restriction S1 → Y
def restrict_further {X Y: Type*} {S1 S2: Set X} (h: S1 ⊆ S2) (f: S2 → Y): S1 → Y :=
  fun ⟨x, hx⟩ => f ⟨x, h hx⟩

-- Given two blocks b1 = (Ω1, f1) and b2 = (Ω2, f2)
-- Define b1 ≤ b2 if Ω1 ⊆ Ω2 and f2|Ω1 = f1
class Block_le {X Y: Type*} (b1 b2: Block X Y): Prop where
  sub: b1.fst ⊆ b2.fst
  res: restrict_further sub b2.snd = b1.snd

-- For every u: X → Y and Ω ⊆ X we have (Ω, u|Ω) ≤ (X, u|X)
theorem Block_induced_le (u: X → Y) (Ω: Set X):
  Block_le (Block_induced u Ω) (Block_univ u) := {
    sub := by simp [Block_univ, Block_induced]
    res := rfl
  }

theorem Block_le_refl {X Y: Type*} (b: Block X Y): Block_le b b := {
  sub := by rfl
  res := rfl
}

theorem Block_le_trans {X Y: Type*} (b1 b2 b3: Block X Y) (h1: Block_le b1 b2) (h2: Block_le b2 b3): Block_le b1 b3 := {
  sub := le_trans h1.sub h2.sub
  res := by
    rw [←h1.res, ←h2.res]
    congr
}

theorem Block_le_antisymm {X Y: Type*} (b1 b2: Block X Y) (h1: Block_le b1 b2) (h2: Block_le b2 b1): b1 = b2 := by
  apply Sigma.eq
  ext x
  simp
  sorry
  exact le_antisymm h1.sub h2.sub

-- show that BlockLeq forms a preorder
instance {X Y: Type*}: PartialOrder (Block X Y) := {
  le := Block_le
  le_refl := Block_le_refl
  le_trans := Block_le_trans
  le_antisymm := Block_le_antisymm
}

-- The empty block is the bottom of the Block_le relation
theorem empty_block_bot {X Y: Type*}: IsBot (Block_empty X Y) := by
  intro b
  constructor
  simp [Block_empty]
  sorry
  simp [Block_empty]

-- Relation between eqOn_nhd and blocks: V(u, Ω) = {v | the block (Ω, uΩ) appears in v}
/-
theorem block_eqOn_nhd_eq (u: X → Y) (Ω: Set X): eqOn_nhd u Ω = {v: X → Y | appears v ⟨Ω, Ω.restrict u⟩} := by
  simp [eqOn_nhd, appears]
  ext
  constructor <;> simp [Set.eqOn_comm]
-/

/-
def setMul [SMul T X] (S: Set T) (x: X): Set X :=
  Set.image (fun s => s • x) S

def setMul2 [SMul T X] (t: T) (S: Set X): Set X :=
  Set.image (fun x => t • x) S

noncomputable def shift_block [Monoid T] [MulAction T X] (t: T): Block X Y → Block X Y := fun ⟨Ω, f⟩ =>
  ⟨
    setMul2 t Ω,
    fun ⟨_, hx⟩ => f ⟨Classical.choose hx, (Classical.choose_spec hx).1⟩
  ⟩
-/

/- The set of blocks found in a configuration -/
def blocks_in_config (u: X → Y): Set (Block X Y) := {b | appears u b}

/- Definition of P(X) -/
def blocks_in_configs (U: Set (X → Y)): Set (Block X Y) :=
  {b | ∃ u ∈ U, appears u b}

/- The set of configs containing a block -/
def configs_containing (b: Block X Y): Set (X → Y) := {u | appears u b}

def Subblock {X Y: Type*} (b: Block X Y) (Ω: Set X) (h: Ω ⊆ b.1): Block X Y :=
  ⟨Ω, fun ⟨x, hx⟩ => b.snd ⟨x, h hx⟩⟩

theorem Subblock_le {X Y: Type*} (b: Block X Y) (Ω: Set X) (h: Ω ⊆ b.1):
  Block_le (Subblock b Ω h) b :=
  ⟨h, rfl⟩

-- two blocks agree if they agree on their shared domain
def Block_agree {X Y: Type*} (b1 b2: Block X Y): Prop :=
  Subblock b1 (b1.fst ∩ b2.fst) Set.inter_subset_left = Subblock b2 (b1.fst ∩ b2.fst) Set.inter_subset_right

-- if b1 ≤ b2 then b1 and b2 agree
theorem Block_le_implies_agree (b1 b2: Block X Y)
  (h: Block_le b1 b2): Block_agree b1 b2 := sorry

theorem Block_univ_agree_iff {X Y: Type*} (u v: X → Y):
  Block_agree (Block_univ u) (Block_univ v) ↔ u = v := by
  simp [Block_agree, Subblock, Block_univ, Block_induced]
  constructor
  intro h
  ext x
  rw [Set.univ_inter] at h
  let h1 := (Sigma.mk.inj_iff.mp h)
  let h2 := h1.2
  simp at h2
  sorry
  intro h
  rw [h]

-- Can we show blocks form a presheaf?

def Section {X: Type*} (Ω: Set X) (Y: Type*): Set (Block X Y) :=
  Set.image (fun u: X → Y => ⟨Ω, Ω.restrict u⟩) Set.univ

def GlobalSection (X Y: Type*): Set (Block X Y) :=
  Section Set.univ Y

def Restriction {V U: Set X} (h: U ⊆ V):
  Section V Y → Section U Y := sorry
