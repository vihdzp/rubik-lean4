import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.Defs
import Rubik.Equiv
import Rubik.Orientation

/-!
Defines structures for the pieces in a Rubik's cube.

A Rubik's cube is traditionally considered to have 6 center pieces, 12 edge pieces, and 8 corner
pieces. For our mathematical formalization, it's useful to be more granular.

We ignore center pieces, as they're always fixed in place, and subdivide the edges and corners into
their individual stickers. This gives us 24 `EdgePiece`s and 24 `CornerPiece`s, which can be
identified with `IsAdjacent` oriented pairs, and `IsAdjacent₃` oriented triples, so that
permutations of these tuples yield the other pieces in the same edge or corner. See the docs there
for details on this assignment.

`Edge` and `Corner` are then defined as quotients of `EdgePiece` and `CornerPiece` under the
relation of being in the same edge or corner. As expected, there are `8` `Edge`s and `12` `Corner`s.
-/

open Orientation

/-- An edge piece is an ordered pair of adjacent orientations.

Since we identify colors and orientations, there's two possible ways to think of this structure:

- The position of an edge piece within a Rubik's cube, specified by its face, followed by its
  relative orientation with respect to it. For instance, `EdgePiece.mk U B` is the upper piece in
  the upper-back edge.
- An edge piece with a particular color, within a particular edge. For instance,
  `EdgePiece.mk U B` is the white piece of the white-blue edge.

The type `PRubik` contains a `Perm EdgePiece` field, which assigns to each edge piece position in
the cube a particular sticker. -/
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

protected theorem ne (e : EdgePiece) : e.fst ≠ e.snd :=
  e.isAdjacent.ne

-- Not marked as `ext` since it creates undesirable goals with `PRubik.ext`.
theorem ext {e₁ e₂ : EdgePiece} (hf : e₁.fst = e₂.fst) (hs : e₁.snd = e₂.snd) : e₁ = e₂ := by
  cases e₁
  cases e₂
  simpa using ⟨hf, hs⟩

theorem ext_iff {e₁ e₂ : EdgePiece} : e₁ = e₂ ↔ e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hf, hs⟩
    exact ext hf hs

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder EdgePiece :=
  LinearOrder.lift' (fun e ↦ [e.fst, e.snd]) (fun _ _ ↦ by simp [ext_iff])

/-- Builds an `EdgePiece`, automatically inferring the adjacency condition. -/
protected abbrev mk' (a b : Orientation) (h : IsAdjacent a b := by decide) : EdgePiece :=
  EdgePiece.mk a b h

/-- Constructs the other edge piece sharing an edge. -/
def flip (e : EdgePiece) : EdgePiece :=
  ⟨_, _, e.isAdjacent.symm⟩

@[simp]
theorem flip_mk (h : IsAdjacent a b) : flip ⟨a, b, h⟩ = ⟨b, a, h.symm⟩ :=
  rfl

@[simp]
theorem flip_fst (e : EdgePiece) : e.flip.fst = e.snd :=
  rfl

@[simp]
theorem flip_snd (e : EdgePiece) : e.flip.snd = e.fst :=
  rfl

@[simp]
theorem flip₂ (e : EdgePiece) : e.flip.flip = e :=
  rfl

@[simp]
theorem flip_inj {e₁ e₂ : EdgePiece} : e₁.flip = e₂.flip ↔ e₁ = e₂ :=
  (Function.LeftInverse.injective flip₂).eq_iff

theorem flip_ne (e : EdgePiece) : e.flip ≠ e := by
  rw [ne_eq, EdgePiece.ext_iff, flip_fst, flip_snd, not_and]
  intro h
  cases e.isAdjacent.ne h.symm

/-- Constructs the finset containing the edge's orientations. -/
def toFinset (e : EdgePiece) : Finset Orientation :=
  ⟨{e.fst, e.snd}, by simpa using e.isAdjacent.ne⟩

theorem toFinset_val (e : EdgePiece) : e.toFinset.val = {e.fst, e.snd} :=
  rfl

theorem mem_toFinset {e : EdgePiece} : a ∈ e.toFinset ↔ a = e.fst ∨ a = e.snd := by
  rw [toFinset]
  simp

@[simp]
theorem flip_toFinset (e : EdgePiece) : e.flip.toFinset = e.toFinset := by
  rw [toFinset]
  simp_rw [Multiset.pair_comm]
  rfl

/-- Returns the unique edge piece sharing a edge, with the given orientation.

If the edge does not contain the orientation, we return some dummy edge piece. -/
def withOrientation (e : EdgePiece) (a : Orientation) : EdgePiece :=
  if e.fst = a then e else if e.snd = a then e.flip else default

theorem withOrientation_fst (e : EdgePiece) (ha : a ∈ e.toFinset) :
    (e.withOrientation a).fst = a := by
  rw [withOrientation]
  obtain rfl | rfl := mem_toFinset.1 ha
  · rw [if_pos rfl]
  · rw [if_neg e.isAdjacent.ne, if_pos rfl, flip_fst]

@[simp]
theorem withOrientation_flip (e : EdgePiece) : e.flip.withOrientation a = e.withOrientation a := by
  rw [withOrientation, withOrientation]
  by_cases ha : a ∈ e.toFinset
  · have h := e.isAdjacent.ne
    obtain rfl | rfl := mem_toFinset.1 ha <;>
    simp [h, h.symm]
  · rw [mem_toFinset, not_or] at ha
    simp [Ne.symm ha.1, Ne.symm ha.2]

instance : Setoid EdgePiece where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans

theorem equiv_def {e₁ e₂ : EdgePiece} : e₁ ≈ e₂ ↔ e₁.toFinset = e₂.toFinset :=
  Iff.rfl

theorem equiv_iff : ∀ {e₁ e₂ : EdgePiece}, e₁ ≈ e₂ ↔ e₁ = e₂ ∨ e₁ = e₂.flip := by
  simp_rw [equiv_def]
  decide

-- TODO: change to this once `perm_pair_iff` drops.
/-simp_rw [equiv_def, ← Finset.val_inj, toFinset_val, EdgePiece.ext_iff]
change Multiset.ofList _ = Multiset.ofList _ ↔ _
simp-/

instance : DecidableRel (α := EdgePiece) (· ≈ ·) :=
  fun _ _ ↦ decidable_of_iff _ equiv_iff.symm

theorem flip_equiv (e : EdgePiece) : e.flip ≈ e :=
  e.flip_toFinset

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

/-- Builds an `Edge`, automatically inferring the adjacency condition. -/
protected abbrev mk (a b : Orientation) (h : IsAdjacent a b := by decide) : Edge :=
  ⟦EdgePiece.mk a b h⟧

@[simp]
theorem mk_flip (e : EdgePiece) : (⟦e.flip⟧ : Edge) = ⟦e⟧ :=
  Quotient.sound e.flip_equiv

/-- Constructs the finset containing the edge's orientations. -/
def toFinset : Edge → Finset Orientation :=
  Quotient.lift EdgePiece.toFinset (fun _ _ ↦ id)

@[simp]
theorem toFinset_mk (e : EdgePiece) : toFinset ⟦e⟧ = e.toFinset :=
  rfl

theorem toFinset_injective : Function.Injective toFinset := by
  intro e₁ e₂
  refine Quotient.inductionOn₂ e₁ e₂ ?_
  intro e₁ e₂ h
  rwa [toFinset_mk, toFinset_mk, ← EdgePiece.equiv_def, ← Quotient.eq] at h

@[simp]
theorem toFinset_inj (e₁ e₂ : Edge) : e₁.toFinset = e₂.toFinset ↔ e₁ = e₂ :=
  toFinset_injective.eq_iff

unsafe instance : Repr Edge :=
  ⟨fun e _ ↦ repr e.toFinset⟩

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder Edge :=
  LinearOrder.lift' (fun e ↦ Finset.Colex.toColex e.toFinset) (fun _ _ ↦ by simp)

/-- Given an edge and an orientation it contains, you can recover a unique edge piece within that
edge with that orientation.

If the edge does not contain the orientation, we return some dummy edge piece. -/
def toEdgePiece (e : Edge) (a : Orientation) : EdgePiece :=
  e.lift (fun e ↦ EdgePiece.withOrientation e a) (by
    intro _ _ h
    obtain rfl | rfl := EdgePiece.equiv_iff.1 h <;>
    simp
  )

/-- Returns the permutation of edge pieces resulting from flipping a given edge. -/
def flipEquiv (e : Edge) : Equiv.Perm EdgePiece :=
  e.lift (fun e ↦ Equiv.swap e e.flip) (by
    intro _ _ h
    obtain rfl | rfl := EdgePiece.equiv_iff.1 h
    · rfl
    · dsimp
      rw [Equiv.swap_comm]
  )

@[simp]
theorem flipEquiv_mk (e : EdgePiece) : flipEquiv ⟦e⟧ = Equiv.swap e e.flip :=
  rfl

theorem flipEquiv_of_ne {e : Edge} {a : EdgePiece} : e ≠ ⟦a⟧ → e.flipEquiv a = a := by
  refine e.inductionOn ?_
  intro e he
  rw [ne_eq, Quotient.eq, @comm _ (· ≈ ·), EdgePiece.equiv_iff, not_or] at he
  rw [flipEquiv_mk, Equiv.swap_apply_of_ne_of_ne he.1 he.2]

@[simp]
theorem mk_flipEquiv (e : Edge) (a : EdgePiece) : ⟦e.flipEquiv a⟧ = (⟦a⟧ : Edge) := by
  obtain rfl | ha := eq_or_ne e ⟦a⟧
  · simp
  · rw [flipEquiv_of_ne ha]

@[simp]
theorem flipEquiv_flip (e : Edge) (a : EdgePiece) : e.flipEquiv a.flip = (e.flipEquiv a).flip := by
  obtain rfl | ha := eq_or_ne e ⟦a⟧
  · simp
  · rw [flipEquiv_of_ne, flipEquiv_of_ne ha]
    rwa [mk_flip]

@[simp]
theorem flipEquiv_flipEquiv (e : Edge) : e.flipEquiv * e.flipEquiv = 1 := by
  refine e.inductionOn ?_
  intro e
  rw [flipEquiv_mk, Equiv.swap_mul_self]

end Edge

/-- A corner piece is an ordered triple of pairwise adjacent orientations, oriented as the standard
basis.

Since we identify colors and orientations, there's two possible ways to think of this type:

- The position of a corner piece within a Rubik's cube, specified by its face, followed by its
  relative orientation with respect to it. For instance, `CornerPiece.mk U B L` is the upper piece
  in the upper-back-left corner.
- A corner piece with a particular color, within a particular corner. For instance,
  `CornerPiece.mk U B L` is the white piece of the white-blue-orange edge.

The type `PRubik` contains a `Perm CornerPiece` field, which assigns to each corner piece position
in the cube a particular sticker. -/
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

namespace CornerPiece

-- Not marked as `ext` since it creates undesirable goals with `PRubik.ext`.
theorem ext {c₁ c₂ : CornerPiece}
    (hf : c₁.fst = c₂.fst) (hs : c₁.snd = c₂.snd) : c₁ = c₂ := by
  obtain ⟨f₁, s₁, t₁, h₁⟩ := c₁
  obtain ⟨f₂, s₂, t₂, h₂⟩ := c₂
  dsimp at *
  subst hf hs
  simpa using h₁.congr h₂

theorem ext_iff {c₁ c₂ : CornerPiece} : c₁ = c₂ ↔ c₁.fst = c₂.fst ∧ c₁.snd = c₂.snd := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hf, hs⟩
    exact ext hf hs

/-- Builds a `CornerPiece`, automatically inferring the adjacency condition. -/
protected abbrev mk' (a b c : Orientation) (h : IsAdjacent₃ a b c := by decide) : CornerPiece :=
  CornerPiece.mk a b c h

theorem isAdjacent (c : CornerPiece) : IsAdjacent c.fst c.snd :=
  c.isAdjacent₃.isAdjacent

/-- Edge pieces and corner pieces can be put in bijection. -/
def _root_.EdgeCornerEquiv : EdgePiece ≃ CornerPiece where
  toFun e := ⟨_, _, _, e.isAdjacent.isAdjacent₃⟩
  invFun c := ⟨_, _, c.isAdjacent⟩
  left_inv _ := rfl
  right_inv _ := ext rfl rfl

instance : Inhabited CornerPiece :=
  ⟨CornerPiece.mk U B L (by decide)⟩

instance : Repr CornerPiece :=
  ⟨fun c ↦ [c.fst, c.snd, c.thd].repr⟩

instance : Fintype CornerPiece :=
  Fintype.ofEquiv _ EdgeCornerEquiv

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder CornerPiece :=
  LinearOrder.lift' _ EdgeCornerEquiv.symm.injective

protected theorem ne (c : CornerPiece) : c.fst ≠ c.snd ∧ c.snd ≠ c.thd ∧ c.thd ≠ c.fst :=
  c.isAdjacent₃.ne

/-- Permutes the colors in a corner cyclically. -/
def cyclic (c : CornerPiece) : CornerPiece :=
  ⟨_, _, _, c.isAdjacent₃.cyclic⟩

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

@[simp]
theorem cyclic₃ (c : CornerPiece) : c.cyclic.cyclic.cyclic = c :=
  rfl

@[simp]
theorem cyclic_inj {c₁ c₂ : CornerPiece} : c₁.cyclic = c₂.cyclic ↔ c₁ = c₂ := by
  constructor
  · exact congr_arg (cyclic ∘ cyclic)
  · rintro rfl
    rfl

theorem cyclic_ne (c : CornerPiece) : c.cyclic ≠ c := by
  rw [ne_eq, ext_iff, not_and, cyclic_fst]
  intro h
  cases c.isAdjacent.ne h.symm

theorem cyclic_cyclic_ne (c : CornerPiece) : c.cyclic.cyclic ≠ c :=
  (cyclic_ne c.cyclic.cyclic).symm

theorem axis_thd (c : CornerPiece) : c.thd.axis = c.fst.axis.other c.snd.axis := by
  rw [c.isAdjacent₃.eq_cross, axis_cross]

/-- Constructs the finset containing the corner's orientations. -/
def toFinset (e : CornerPiece) : Finset Orientation :=
  ⟨{e.fst, e.snd, e.thd}, by
    obtain ⟨h₁, h₂, h₃⟩ := e.isAdjacent₃.ne
    simpa using ⟨⟨h₁, h₃.symm⟩, h₂⟩⟩

theorem toFinset_val (c : CornerPiece) : c.toFinset.val = {c.fst, c.snd, c.thd} :=
  rfl

theorem mem_toFinset {c : CornerPiece} : a ∈ c.toFinset ↔ a = c.fst ∨ a = c.snd ∨ a = c.thd := by
  rw [toFinset]
  simp

@[simp]
theorem cyclic_toFinset (c : CornerPiece) : c.cyclic.toFinset = c.toFinset := by
  have (a b c : Orientation) : ({a, b, c} : Multiset _) = {c, a, b} := by
    change a ::ₘ b ::ₘ c ::ₘ 0 = c ::ₘ a ::ₘ b ::ₘ 0
    rw [Multiset.cons_swap b, Multiset.cons_swap a]
  simp_rw [toFinset, cyclic, this]

/-- Returns the unique corner piece sharing a corner, with the orientation of the given axis. -/
def withAxis (c : CornerPiece) (a : Axis) : CornerPiece :=
  if c.fst.axis = a then c else if c.snd.axis = a then c.cyclic else c.cyclic.cyclic

@[simp]
theorem axis_withAxis_fst (c : CornerPiece) (a : Axis) : (c.withAxis a).fst.axis = a := by
  rw [withAxis]
  split_ifs with h₁ h₂
  · exact h₁
  · rwa [cyclic_fst]
  · rw [cyclic_fst, cyclic_snd, axis_thd, Axis.other_eq_iff c.isAdjacent]
    exact ⟨Ne.symm h₁, Ne.symm h₂⟩

@[simp]
theorem withAxis_cyclic (c : CornerPiece) (a : Axis) : c.cyclic.withAxis a = c.withAxis a := by
  simp [withAxis]
  split_ifs with h₁ h₂ h₃ h₄ h₅ <;>
  try rfl
  · exact (c.isAdjacent (h₁ ▸ h₂)).elim
  · exact (c.cyclic.cyclic.isAdjacent (h₄ ▸ h₃)).elim
  · rw [axis_thd, ← ne_eq, Axis.other_ne_iff c.isAdjacent] at h₃
    obtain rfl | rfl := h₃
    · exact (h₅ rfl).elim
    · exact (h₁ rfl).elim

/-- The "value" of a corner piece is the number of **counterclockwise** rotations needed to orient
a specific face towards its corresponding axis. -/
def value (c : CornerPiece) (a : Axis) : ZMod 3 :=
  if c.fst.axis = a then 0 else if c.thd.axis = a then 1 else 2

theorem value_of_fst {c : CornerPiece} (h : c.fst.axis = a) : c.value a = 0 :=
  if_pos h

theorem value_of_snd {c : CornerPiece} (h : c.snd.axis = a) : c.value a = 2 := by
  have : c.thd.axis ≠ a := (h.symm.trans_ne c.cyclic.isAdjacent).symm
  rw [value, if_neg (ne_of_ne_of_eq c.isAdjacent h), if_neg this]

theorem value_of_thd {c : CornerPiece} (h : c.thd.axis = a) : c.value a = 1 := by
  have : c.fst.axis ≠ a := (h.symm.trans_ne c.cyclic.cyclic.isAdjacent).symm
  rw [value, if_neg this, if_pos h]

@[simp]
theorem value_withAxis (c : CornerPiece) (a : Axis) : (c.withAxis a).value a = 0 :=
  value_of_fst (axis_withAxis_fst c a)

@[simp]
theorem value_cyclic (c : CornerPiece) (a : Axis) : c.cyclic.value a = c.value a + 1 := by
  rw [value]
  split_ifs with h₁ h₂
  · rw [value_of_snd h₁]
    rfl
  · rw [value_of_fst h₂, zero_add]
  · rw [value_of_thd, one_add_one_eq_two]
    rw [c.isAdjacent₃.eq_cross, axis_cross, Axis.other_eq_iff c.isAdjacent]
    exact ⟨Ne.symm h₂, Ne.symm h₁⟩

instance : Setoid CornerPiece where
  r c₁ c₂ := c₁.toFinset = c₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans

theorem equiv_def {c₁ c₂ : CornerPiece} : c₁ ≈ c₂ ↔ c₁.toFinset = c₂.toFinset :=
  Iff.rfl

theorem equiv_iff : ∀ {c₁ c₂ : CornerPiece},
    c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁.cyclic = c₂ := by
  simp_rw [equiv_def]
  decide

theorem equiv_iff' {c₁ c₂ : CornerPiece} :
    c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁ = c₂.cyclic.cyclic := by
  rw [equiv_iff]
  convert Iff.rfl using 3
  rw [← cyclic_inj, cyclic₃]

instance : DecidableRel (α := CornerPiece) (· ≈ ·) :=
  fun _ _ ↦ decidable_of_iff _ equiv_iff.symm

theorem cyclic_equiv (c : CornerPiece) : c.cyclic ≈ c :=
  c.cyclic_toFinset

theorem withAxis_equiv (c : CornerPiece) (a : Axis) : c.withAxis a ≈ c := by
  rw [withAxis]
  split_ifs
  · rfl
  · exact cyclic_equiv c
  · exact (cyclic_equiv _).trans (cyclic_equiv c)

theorem withAxis_eq_of_equiv {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) (a : Axis) :
    c₁.withAxis a = c₂.withAxis a := by
  obtain rfl | rfl | rfl := equiv_iff.1 h
  · rfl
  · rw [withAxis_cyclic]
  · rw [withAxis_cyclic]

theorem eq_of_value_eq {c₁ c₂ : CornerPiece} {a : Axis} (hc : c₁ ≈ c₂)
    (h : c₁.value a = c₂.value a) : c₁ = c₂ := by
  rw [equiv_iff] at hc
  obtain rfl | rfl | rfl := hc
  · rfl
  · simp at h
    contradiction
  · simp at h
    contradiction

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

/-- Builds a `Corner`, automatically inferring the adjacency condition. -/
protected abbrev mk (a b c : Orientation) (h : IsAdjacent₃ a b c := by decide) : Corner :=
  ⟦CornerPiece.mk a b c h⟧

@[simp]
theorem mk_cyclic (c : CornerPiece) : (⟦c.cyclic⟧ : Corner) = ⟦c⟧ :=
  Quotient.sound c.cyclic_toFinset

/-- Constructs the finset containing the edge's orientations. -/
def toFinset : Corner → Finset Orientation :=
  Quotient.lift CornerPiece.toFinset (fun _ _ ↦ id)

@[simp]
theorem toFinset_mk (c : CornerPiece) : toFinset ⟦c⟧ = c.toFinset :=
  rfl

theorem toFinset_injective : Function.Injective toFinset := by
  intro c₁ c₂
  refine Quotient.inductionOn₂ c₁ c₂ ?_
  intro c₁ c₂ h
  rwa [toFinset_mk, toFinset_mk, ← CornerPiece.equiv_def, ← Quotient.eq] at h

@[simp]
theorem toFinset_inj (c₁ c₂ : Corner) : c₁.toFinset = c₂.toFinset ↔ c₁ = c₂ :=
  toFinset_injective.eq_iff

unsafe instance : Repr Corner :=
  ⟨fun c _ ↦ repr c.toFinset⟩

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder Corner :=
  LinearOrder.lift' (fun c ↦ Finset.Colex.toColex c.toFinset) (fun _ _ ↦ by simp)

/-- Given a corner and an axis, you can recover a unique corner piece within that corner with that
axis. -/
def toCornerPiece (c : Corner) (a : Axis) : CornerPiece :=
  c.lift (fun c ↦ CornerPiece.withAxis c a) (by
    intro _ _ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;>
    simp
  )

@[simp]
theorem toCornerPiece_mk (c : CornerPiece) (a : Axis) : toCornerPiece ⟦c⟧ a = c.withAxis a :=
  rfl

@[simp]
theorem axis_toCornerPiece (c : Corner) (a : Axis) : (c.toCornerPiece a).fst.axis = a := by
  refine c.inductionOn ?_
  intro c
  rw [toCornerPiece_mk, CornerPiece.axis_withAxis_fst]

@[simp]
theorem mk_toCornerPiece (c : Corner) (a : Axis) : ⟦c.toCornerPiece a⟧ = c := by
  refine c.inductionOn ?_
  intro c
  rw [toCornerPiece_mk, Quotient.eq]
  exact CornerPiece.withAxis_equiv c a

@[simp]
theorem value_toCornerPiece (c : Corner) (a : Axis) : (c.toCornerPiece a).value a = 0 := by
  refine c.inductionOn ?_
  intro c
  rw [toCornerPiece_mk, CornerPiece.value_withAxis]

/-- Returns the permutation of corner pieces resulting from rotating a given corner
**clockwise**. -/
def rotateEquiv (c : Corner) : Equiv.Perm CornerPiece :=
  c.lift (fun c ↦ Equiv.cycle c c.cyclic c.cyclic.cyclic) (by
    intro _ _ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;>
      dsimp <;>
      repeat rw [Equiv.cycle_cyclic]
  )

@[simp]
theorem rotateEquiv_mk (c : CornerPiece) :
    rotateEquiv ⟦c⟧ = Equiv.cycle c c.cyclic c.cyclic.cyclic :=
  rfl

theorem rotateEquiv_of_ne {c : Corner} {a : CornerPiece} : c ≠ ⟦a⟧ → c.rotateEquiv a = a := by
  refine c.inductionOn ?_
  intro c hc
  rw [ne_eq, Quotient.eq, @comm _ (· ≈ ·), CornerPiece.equiv_iff', not_or, not_or] at hc
  rw [rotateEquiv_mk, Equiv.cycle_apply_of_ne hc.1 hc.2.1 hc.2.2]

@[simp]
theorem mk_rotateEquiv (c : Corner) (a : CornerPiece) : ⟦c.rotateEquiv a⟧ = (⟦a⟧ : Corner) := by
  obtain rfl | ha := eq_or_ne c ⟦a⟧
  · rw [rotateEquiv_mk, Quotient.eq, Equiv.cycle_fst]
    · exact a.cyclic_equiv
    · rw [ne_eq, CornerPiece.cyclic_inj]
      exact a.cyclic_ne.symm
    · exact a.cyclic_cyclic_ne
  · rw [rotateEquiv_of_ne ha]

@[simp]
theorem rotateEquiv_cyclic (c : Corner) (a : CornerPiece) :
    c.rotateEquiv a.cyclic = (c.rotateEquiv a).cyclic := by
  obtain rfl | ha := eq_or_ne c ⟦a⟧
  · rw [rotateEquiv_mk, Equiv.cycle_fst a.cyclic.cyclic_ne.symm a.cyclic_cyclic_ne,
      Equiv.cycle_snd a.cyclic_ne.symm a.cyclic_cyclic_ne]
  · rw [rotateEquiv_of_ne, rotateEquiv_of_ne ha]
    rwa [mk_cyclic]

end Corner
