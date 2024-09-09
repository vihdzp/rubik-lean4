import Rubik.Orientation

open Orientation

/-- An edge piece is an ordered pair of adjacent orientations.

Since we identify colors and orientations, there's two possible ways to think of this type:

- The position of an edge piece within a Rubik's cube, specified by its face, followed by its
  relative orientation with respect to it. For instance, `EdgePiece.mk U B _` is the upper piece in the upper-back edge.
- An edge piece with a particular color, within a particular edge. For instance,
  `EdgePiece.mk U B _` is the white piece of the white-blue edge.

The type `PRubik` contains an `EdgePiece ≃ EdgePiece` field, which assigns to each position in the
cube a particular sticker color. -/
structure EdgePiece : Type where
  /-- The first and "distinguished" orientation in the edge piece. -/
  fst : Orientation
  /-- The second orientation in the edge piece. -/
  snd : Orientation
  /-- Both orientations are adjacent. -/
  isAdjacent : IsAdjacent fst snd

deriving instance DecidableEq, Fintype for EdgePiece

namespace EdgePiece

instance : Inhabited EdgePiece :=
  ⟨EdgePiece.mk U B (by decide)⟩

instance : Repr EdgePiece :=
  ⟨fun e ↦ [e.fst, e.snd].repr⟩

protected theorem card : Fintype.card EdgePiece = 24 :=
  rfl

protected theorem ne (e : EdgePiece) : e.fst ≠ e.snd :=
  e.isAdjacent.ne

@[ext]
theorem ext {e₁ e₂ : EdgePiece} (hf : e₁.fst = e₂.fst) (hs : e₁.snd = e₂.snd) : e₁ = e₂ := by
  cases e₁
  cases e₂
  simpa using ⟨hf, hs⟩

/-- Builds an `EdgePiece`, automatically inferring the adjacency condition. -/
protected def mk' (a b : Orientation) (h : IsAdjacent a b := by decide) : EdgePiece :=
  EdgePiece.mk a b h

/-- Constructs the other edge piece sharing an edge. -/
def swap (e : EdgePiece) : EdgePiece :=
  ⟨_, _, e.isAdjacent.swap⟩

@[simp]
theorem swap_mk (h : IsAdjacent a b) : swap ⟨a, b, h⟩ = ⟨b, a, h.swap⟩ :=
  rfl

@[simp]
theorem swap_fst (e : EdgePiece) : e.swap.fst = e.snd :=
  rfl

@[simp]
theorem swap_snd (e : EdgePiece) : e.swap.snd = e.fst :=
  rfl

/-- Constructs the finset containing the edge's orientations. -/
def toFinset (e : EdgePiece) : Finset Orientation :=
  ⟨{e.fst, e.snd}, by simpa using e.isAdjacent.ne⟩

theorem card_toFinset (e : EdgePiece) : e.toFinset.card = 2 :=
  rfl

theorem toFinset_val (e : EdgePiece) : e.toFinset.val = {e.fst, e.snd} :=
  rfl

theorem mem_toFinset (e : EdgePiece) (a : Orientation) :
    a ∈ e.toFinset ↔ a = e.fst ∨ a = e.snd := by
  rw [toFinset]
  simp

@[simp]
theorem swap_toFinset (e : EdgePiece) : e.swap.toFinset = e.toFinset := by
  rw [toFinset]
  simp_rw [Multiset.pair_comm]
  rfl

instance : Setoid EdgePiece where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans

instance : DecidableRel (α := EdgePiece) (· ≈ ·) :=
  fun e₁ e₂ ↦ inferInstanceAs (Decidable (e₁.toFinset = e₂.toFinset))

theorem equiv_def {e₁ e₂ : EdgePiece} : e₁ ≈ e₂ ↔ e₁.toFinset = e₂.toFinset :=
  Iff.rfl

theorem equiv_iff : ∀ {e₁ e₂ : EdgePiece}, e₁ ≈ e₂ ↔ e₁ = e₂ ∨ e₁ = e₂.swap := by
  decide

-- TODO: change to this once `perm_pair_iff` drops.
/-simp_rw [equiv_def, ← Finset.val_inj, toFinset_val, EdgePiece.ext_iff]
change Multiset.ofList _ = Multiset.ofList _ ↔ _
simp-/

theorem equiv_swap (e : EdgePiece) : e.swap ≈ e :=
  e.swap_toFinset

end EdgePiece

/-- An edge is the equivalence class of edge pieces sharing an edge. -/
def Edge : Type := Quotient EdgePiece.instSetoid

namespace Edge

instance : Inhabited Edge :=
  Quotient.instInhabitedQuotient _

instance : DecidableEq Edge :=
  Quotient.decidableEq

instance : Fintype Edge :=
  Quotient.fintype _

@[simp]
theorem mk_swap (e : EdgePiece) : (⟦e.swap⟧ : Edge) = ⟦e⟧ :=
  Quotient.sound e.equiv_swap

protected theorem card : Fintype.card Edge = 12 :=
  rfl

end Edge

/-- A corner piece is an ordered triple of pairwise adjacent orientations, oriented as the standard
basis.

Since we identify colors and orientations, there's two possible ways to think of this type:

- The position of a corner piece within a Rubik's cube, specified by its face, followed by its
  relative orientation with respect to it. For instance, `EdgePiece.mk U B L _` is the upper piece
  in the upper-back-left corner.
- A corner piece with a particular color, within a particular corner. For instance,
  `EdgePiece.mk U B L _` is the white piece of the white-blue-orange edge.

The type `PRubik` contains an `CornerPiece ≃ CornerPiece` field, which assigns to each position in
the cube a particular sticker color. -/
structure CornerPiece : Type where
  /-- The first and "distinguished" orientation in the corner piece. -/
  fst : Orientation
  /-- The second orientation in the corner piece. -/
  snd : Orientation
  /-- The third orientation in the corner piece. This is actually completely determined from the
  other two, but we still define it for symmetry. -/
  thd : Orientation
  /-- All orientations are adjacent, and form a positively oriented basis. -/
  isAdjacent₃ : IsAdjacent₃ fst snd thd

deriving instance DecidableEq for CornerPiece

/-- Builds a corner from pairwise isAdjacent orientations. -/
def Orientation.IsAdjacent₃.toCornerPiece (h : IsAdjacent₃ a b c) : CornerPiece :=
  CornerPiece.mk a b c h

@[ext]
theorem CornerPiece.ext {c₁ c₂ : CornerPiece}
    (hf : c₁.fst = c₂.fst) (hs : c₁.snd = c₂.snd) : c₁ = c₂ := by
  obtain ⟨f₁, s₁, t₁, h₁⟩ := c₁
  obtain ⟨f₂, s₂, t₂, h₂⟩ := c₂
  dsimp at *
  subst hf hs
  simpa using h₁.congr h₂

/-- Edge pieces and corner pieces can be put in bijection. -/
def EdgeCornerEquiv : EdgePiece ≃ CornerPiece where
  toFun e := ⟨_, _, _, e.isAdjacent.isAdjacent₃⟩
  invFun c := ⟨_, _, c.isAdjacent₃.isAdjacent⟩
  left_inv _ := rfl
  right_inv c := by ext <;> rfl

namespace CornerPiece

instance : Inhabited CornerPiece :=
  ⟨CornerPiece.mk U B L (by decide)⟩

instance : Repr CornerPiece :=
  ⟨fun c ↦ [c.fst, c.snd, c.thd].repr⟩

instance : Fintype CornerPiece :=
  Fintype.ofEquiv _ EdgeCornerEquiv

protected theorem card : Fintype.card CornerPiece = 24 :=
  rfl

protected theorem ne (c : CornerPiece) : c.fst ≠ c.snd ∧ c.snd ≠ c.thd ∧ c.thd ≠ c.fst :=
  c.isAdjacent₃.ne

/-- Permutes the colors in a corner cyclically. -/
def cyclic (c : CornerPiece) : CornerPiece :=
  c.isAdjacent₃.cyclic.toCornerPiece

@[simp]
theorem cyclic_mk (h : IsAdjacent₃ a b c) : cyclic ⟨a, b, c, h⟩ = ⟨b, c, a, h.cyclic⟩ :=
  rfl

@[simp]
theorem cyclic_fst (c : CornerPiece) : c.cyclic.fst = c.snd :=
  rfl

@[simp]
theorem cyclic_snd (c : CornerPiece) : c.cyclic.snd = c.thd :=
  rfl

@[simp]
theorem cyclic_thd (c : CornerPiece) : c.cyclic.thd = c.fst :=
  rfl

/-- Constructs the finset containing the corner's orientations. -/
def toFinset (e : CornerPiece) : Finset Orientation :=
  ⟨{e.fst, e.snd, e.thd}, by
    obtain ⟨h₁, h₂, h₃⟩ := e.isAdjacent₃.ne
    simpa using ⟨⟨h₁, h₃.symm⟩, h₂⟩⟩

theorem card_toFinset (c : CornerPiece) : c.toFinset.card = 3 :=
  rfl

theorem toFinset_val (c : CornerPiece) : c.toFinset.val = {c.fst, c.snd, c.thd} :=
  rfl

theorem mem_toFinset (c : CornerPiece) (a : Orientation) :
    a ∈ c.toFinset ↔ a = c.fst ∨ a = c.snd ∨ a = c.thd := by
  rw [toFinset]
  simp

@[simp]
theorem cyclic_toFinset (c : CornerPiece) : c.cyclic.toFinset = c.toFinset := by
  have (a b c : Orientation) : ({a, b, c} : Multiset _) = {c, a, b} := by
    change a ::ₘ b ::ₘ c ::ₘ 0 = c ::ₘ a ::ₘ b ::ₘ 0
    rw [Multiset.cons_swap b, Multiset.cons_swap a]
  simp_rw [toFinset, cyclic, IsAdjacent₃.toCornerPiece, this]

instance : Setoid CornerPiece where
  r c₁ c₂ := c₁.toFinset = c₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans

instance : DecidableRel (α := CornerPiece) (· ≈ ·) :=
  fun c₁ c₂ ↦ inferInstanceAs (Decidable (c₁.toFinset = c₂.toFinset))

theorem equiv_def {c₁ c₂ : CornerPiece} : c₁ ≈ c₂ ↔ c₁.toFinset = c₂.toFinset :=
  Iff.rfl

theorem equiv_iff : ∀ {c₁ c₂ : CornerPiece},
    c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁.cyclic = c₂ := by
  decide

theorem equiv_cyclic (c : CornerPiece) : c.cyclic ≈ c :=
  c.cyclic_toFinset

end CornerPiece

/-- A corner is the equivalence class of corner pieces sharing a corner. -/
def Corner : Type := Quotient CornerPiece.instSetoid

namespace Corner

instance : Inhabited Corner :=
  Quotient.instInhabitedQuotient _

instance : DecidableEq Corner :=
  Quotient.decidableEq

instance : Fintype Corner :=
  Quotient.fintype _

@[simp]
theorem mk_cyclic (c : CornerPiece) : (⟦c.cyclic⟧ : Corner) = ⟦c⟧ :=
  Quotient.sound c.cyclic_toFinset

protected theorem card : Fintype.card Corner = 8 :=
  rfl

end Corner
