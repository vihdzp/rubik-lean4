import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod

/-- A Cartesian axis in 3D space. -/
inductive Axis : Type
  /-- The `x` or left-right axis. -/
  | x : Axis
  /-- The `y` or bottom-top axis. -/
  | y : Axis
  /-- The `z` or back-front axis. -/
  | z : Axis

deriving instance DecidableEq, Fintype for Axis

namespace Axis

instance : Repr Axis := ⟨fun e _ ↦ Std.Format.text <| match e with
  | Axis.x => "X"
  | Axis.y => "Y"
  | Axis.z => "Z"
⟩

protected theorem card : Fintype.card Axis = 3 :=
  rfl

/-- Permutes the `x`, `y`, `z` axes in cyclic order. -/
def rotate : Axis → Axis
  | Axis.x => Axis.y
  | Axis.y => Axis.z
  | Axis.z => Axis.x

theorem rotate_ne : ∀ a : Axis, a.rotate ≠ a := by
  decide

@[simp]
theorem rotate_inj : ∀ {a b : Axis}, a.rotate = b.rotate ↔ a = b := by
  decide

/-- Whether `b` is the next axis in cyclic order to `a`. -/
def IsNext (a b : Axis) : Prop :=
  a.rotate = b

instance : DecidableRel IsNext :=
  inferInstanceAs (∀ a b : Axis, Decidable (a.rotate = b))

theorem isNext_irrefl (a : Axis) : ¬ IsNext a a :=
  rotate_ne a

@[simp]
theorem isNext_asymm_iff : ∀ {a b}, a ≠ b → (¬ IsNext a b ↔ IsNext b a) := by
  decide

theorem IsNext.asymm (h : IsNext a b) : ¬ IsNext b a := by
  obtain rfl | hn := eq_or_ne b a
  · exact isNext_irrefl b
  · exact (isNext_asymm_iff hn).2 h

@[simp]
theorem isNext_rotate : ∀ {a b}, IsNext a.rotate b.rotate ↔ IsNext a b := by
  decide

theorem IsNext.congr_left (hb : IsNext a b) (hc : IsNext a c) : b = c :=
  hb.symm.trans hc

theorem IsNext.congr_right (ha : IsNext a c) (hb : IsNext b c) : a = b :=
  rotate_inj.1 <| ha.trans hb.symm

/-- Given two distinct axes, returns the third. If both axes are equal, we just return it. -/
def other : Axis → Axis → Axis
  | Axis.x, Axis.y => Axis.z
  | Axis.x, Axis.z => Axis.y
  | Axis.y, Axis.x => Axis.z
  | Axis.y, Axis.z => Axis.x
  | Axis.z, Axis.x => Axis.y
  | Axis.z, Axis.y => Axis.x
  | Axis.x, Axis.x => Axis.x
  | Axis.y, Axis.y => Axis.y
  | Axis.z, Axis.z => Axis.z

@[simp]
theorem other_self : ∀ a, other a a = a := by
  decide

@[simp]
theorem other_eq_left_iff : ∀ {a b}, other a b = a ↔ a = b := by
  decide

@[simp]
theorem other_eq_right_iff : ∀ {a b}, other a b = b ↔ a = b := by
  decide

theorem other_eq_iff : ∀ {a b c}, a ≠ b → (other a b = c ↔ c ≠ a ∧ c ≠ b) := by
  decide

theorem other_eq (h₁ : a ≠ b) (h₂ : c ≠ a) (h₃ : c ≠ b) : other a b = c :=
  (other_eq_iff h₁).2 ⟨h₂, h₃⟩

theorem other_ne_iff (h : a ≠ b) : other a b ≠ c ↔ c = a ∨ c = b := by
  rw [← not_iff_not, not_ne_iff, other_eq_iff h, not_or]

theorem other_comm : ∀ a b, other a b = other b a := by
  decide

theorem other_ne_left (h : a ≠ b) : other a b ≠ a :=
  ((other_eq_iff h).1 rfl).1

theorem other_ne_right (h : a ≠ b) : other a b ≠ b :=
  ((other_eq_iff h).1 rfl).2

@[simp]
theorem other_other_left : ∀ {a b}, other (other a b) a = b := by
  decide

@[simp]
theorem other_other_right : ∀ {a b}, other (other a b) b = a := by
  decide

@[simp]
theorem other_other_left' : other a (other a b) = b := by
  rw [other_comm, other_other_left]

@[simp]
theorem other_other_right' : other b (other a b) = a := by
  rw [other_comm, other_other_right]

@[simp]
theorem other_inj_left : ∀ {a b c}, other c a = other c b ↔ a = b := by
  decide

@[simp]
theorem other_inj_right : other a c = other b c ↔ a = b := by
  rw [other_comm, @other_comm b, other_inj_left]

@[simp]
theorem other_isNext_left : ∀ {a b}, (other a b).IsNext a ↔ a.IsNext b := by
  decide

@[simp]
theorem other_isNext_right : ∀ {a b}, (other a b).IsNext b ↔ b.IsNext a := by
  decide

@[simp]
theorem isNext_other_left : ∀ {a b}, IsNext a (other a b) ↔ b.IsNext a := by
  decide

@[simp]
theorem isNext_other_right : ∀ {a b}, IsNext b (other a b) ↔ a.IsNext b := by
  decide

end Axis

/-- One of six possible orientations for a face of a Rubik's cube, represented as `Bool × Axis`.

We employ the convention that the sign argument is `true` for the front, right, and up orientations.

This type will also be used for the colors in a Rubik's cube, using the following convention:

* Red = Right
* White = Up
* Green = Front
* Orange = Left
* Yellow = Down
* Blue = Back
-/
def Orientation : Type := Bool × Axis

namespace Orientation

instance decEq : DecidableEq Orientation :=
  inferInstanceAs (DecidableEq (Bool × Axis))

instance : Repr Orientation := ⟨fun e _ ↦ Std.Format.text <| match e with
  | (true, Axis.x) => "R"
  | (true, Axis.y) => "U"
  | (true, Axis.z) => "F"
  | (false, Axis.x) => "L"
  | (false, Axis.y) => "D"
  | (false, Axis.z) => "B"
⟩

/-- The color represented by an orientation, as a Unicode square. -/
def color : Orientation → String
  | (true, Axis.x) => "🟥"
  | (true, Axis.y) => "⬜"
  | (true, Axis.z) => "🟩"
  | (false, Axis.x) => "🟧"
  | (false, Axis.y) => "🟨"
  | (false, Axis.z) => "🟦"

instance : HAppend Std.Format Orientation Std.Format :=
  ⟨fun s a ↦ s ++ a.color⟩

instance instFintype : Fintype Orientation :=
  inferInstanceAs (Fintype (Bool × Axis))

protected theorem card : Fintype.card Orientation = 6 :=
  rfl

/-- Right orientation or red color. -/
def R : Orientation := (true, Axis.x)
/-- Up orientation or white color. -/
def U : Orientation := (true, Axis.y)
/-- Front orientation or green color. -/
def F : Orientation := (true, Axis.z)

/-- Left orientation or orange color. -/
def L : Orientation := (false, Axis.x)
/-- Down orientation or yellow color. -/
def D : Orientation := (false, Axis.y)
/-- Back orientation or blue color. -/
def B : Orientation := (false, Axis.z)

/-- The sign (positive or negative) corresponding to the orientation. -/
def sign (a : Orientation) : Bool :=
  a.1

@[simp]
theorem sign_mk (b : Bool) (a : Axis) : sign (b, a) = b :=
  rfl

/-- The Cartesian axis corresponding to the orientation. -/
def axis (a : Orientation) : Axis :=
  a.2

@[simp]
theorem axis_mk (b : Bool) (a : Axis) : axis (b, a) = a :=
  rfl

@[ext]
theorem ext (h₁ : sign a = sign b) (h₂ : axis a = axis b) : a = b :=
  Prod.ext h₁ h₂

/-- The negative of an orientation. -/
instance : Neg Orientation :=
  ⟨fun a ↦ (!a.1, a.2)⟩

instance : InvolutiveNeg Orientation :=
  ⟨fun _ ↦ ext (Bool.not_not _) rfl⟩

@[simp]
theorem neg_mk (b : Bool) (a : Axis) : instNeg.neg (b, a) = (!b, a) :=
  rfl

@[simp]
theorem sign_neg (a : Orientation) : (-a).sign = !a.sign :=
  rfl

@[simp]
theorem axis_neg (a : Orientation) : (-a).axis = a.axis :=
  rfl

/-- Two orientations are adjacent when they have distinct axes. -/
def IsAdjacent (a b : Orientation) : Prop :=
  a.axis ≠ b.axis

instance IsAdjacent.decRel : DecidableRel IsAdjacent :=
  inferInstanceAs (∀ a b : Orientation, Decidable (a.axis ≠ b.axis))

@[simp]
theorem neg_isAdjacent : IsAdjacent (-a) b ↔ IsAdjacent a b :=
  Iff.rfl

@[simp]
theorem isAdjacent_neg : IsAdjacent a (-b) ↔ IsAdjacent a b :=
  Iff.rfl

theorem IsAdjacent.ne (h : IsAdjacent a b) : a ≠ b := by
  rintro rfl
  exact h rfl

theorem isAdjacent_comm : IsAdjacent a b ↔ IsAdjacent b a :=
  ne_comm

alias ⟨IsAdjacent.swap, _⟩ := isAdjacent_comm

/-- Given two adjacent orientations, returns the "cross product", i.e. the orientation `c` adjacent
to both, such that `(a, b, c)` is oriented as the standard basis. -/
def cross (a b : Orientation) : Orientation :=
  ((a.axis.IsNext b.axis) == (a.sign == b.sign), a.axis.other b.axis)

@[simp]
theorem sign_cross (a b : Orientation) :
    (cross a b).sign = ((a.axis.IsNext b.axis) == (a.sign == b.sign)) :=
  rfl

@[simp]
theorem axis_cross (a b : Orientation) : (cross a b).axis = a.axis.other b.axis :=
  rfl

theorem IsAdjacent.cross_left (h : IsAdjacent a b) : IsAdjacent (cross a b) a :=
  Axis.other_ne_left h

theorem IsAdjacent.cross_right (h : IsAdjacent a b) : IsAdjacent (cross a b) b :=
  Axis.other_ne_right h

@[simp]
theorem cross_neg_left : ∀ (a b : Orientation), cross (-a) b = -cross a b := by
  decide

@[simp]
theorem cross_neg_right : ∀ (a b : Orientation), cross a (-b) = -cross a b := by
  decide

theorem cross_asymm : ∀ {a b}, IsAdjacent a b → cross a b = - cross b a := by
  decide

@[simp]
theorem cross_inj_left : ∀ {a b c}, cross a c = cross b c ↔ a = b := by
  decide

@[simp]
theorem cross_inj_right : ∀ {a b c}, cross a b = cross a c ↔ b = c := by
  decide

@[simp]
theorem cross_cross_left : ∀ (a b), cross (cross a b) a = b := by
  decide

@[simp]
theorem cross_cross_right : ∀ (a b), cross b (cross a b) = a := by
  decide

theorem cross_cross_left' (h : IsAdjacent a b) : cross a (cross a b) = -b := by
  rw [cross_asymm h, cross_neg_right, cross_cross_right]

theorem cross_cross_right' (h : IsAdjacent a b) : cross (cross a b) b = -a := by
  rw [cross_asymm h, cross_neg_left, cross_cross_left]

/-- Take a piece with stickers on orientations `a ≠ r`, and perform a **counterclockwise** rotation
in orientation `r`. This function returns the new orientation of the sticker with orientation `a`.

For instance, `rotate U F = L` since performing `F'` sends the upper-front corner to the left-front
one.

The reason this is inverted is so that
`(cube.rotate r).edge a b = Cube.edge (a.rotate r) (b.rotate r)`. -/
def rotate (a r : Orientation) : Orientation :=
  if r.axis = a.axis then a else cross r a

theorem rotate_of_eq {a r : Orientation} (h : r.axis = a.axis) : a.rotate r = a :=
  dif_pos h

theorem rotate_of_ne {a r : Orientation} (h : r.axis ≠ a.axis) : a.rotate r = cross r a :=
  dif_neg h

@[simp]
theorem rotate_neg : rotate (-a) r = -rotate a r := by
  by_cases h : r.axis = a.axis
  · rwa [rotate_of_eq h, rotate_of_eq]
  · rwa [rotate_of_ne h, rotate_of_ne, cross_neg_right]

@[simp]
theorem rotate_inj : ∀ {a b r}, rotate a r = rotate b r ↔ a = b := by
  decide

theorem isAdjacent_rotate : ∀ {a b r : Orientation},
    IsAdjacent (a.rotate r) (b.rotate r) ↔ IsAdjacent a b := by
  decide

theorem IsAdjacent.rotate {a b : Orientation} (h : IsAdjacent a b) (r : Orientation) :
    IsAdjacent (a.rotate r) (b.rotate r) :=
  isAdjacent_rotate.2 h

/-- A predicate for three pairwise adjacent orientations, oriented as the standard basis.

The orientation condition is required, since it's not physically possible to exchange two pieces in
a corner without dissassembling it. -/
@[pp_nodot]
def IsAdjacent₃ (a b c : Orientation) : Prop :=
  IsAdjacent a b ∧ c = cross a b

instance IsAdjacent₃.decRel : ∀ a b c, Decidable (IsAdjacent₃ a b c) :=
  inferInstanceAs (∀ a b c, Decidable (IsAdjacent a b ∧ c = cross a b))

theorem IsAdjacent₃.isAdjacent (h : IsAdjacent₃ a b c) : IsAdjacent a b :=
  h.1

theorem IsAdjacent₃.eq_cross (h : IsAdjacent₃ a b c) : c = cross a b :=
  h.2

theorem IsAdjacent.isAdjacent₃ (h : IsAdjacent a b) : IsAdjacent₃ a b (cross a b) :=
  ⟨h, rfl⟩

theorem IsAdjacent₃.congr (h₁ : IsAdjacent₃ a b c₁) (h₂ : IsAdjacent₃ a b c₂) : c₁ = c₂ :=
  h₁.2.trans h₂.2.symm

theorem isAdjacent₃_cyclic : IsAdjacent₃ a b c ↔ IsAdjacent₃ b c a := by
  constructor <;>
  rintro ⟨h, rfl⟩
  · exact ⟨(h.cross_right).symm, (cross_cross_right _ _).symm⟩
  · exact ⟨h.cross_left, (cross_cross_left _ _).symm⟩

alias ⟨IsAdjacent₃.cyclic, _⟩ := isAdjacent₃_cyclic

theorem IsAdjacent₃.ne (h : IsAdjacent₃ a b c) : a ≠ b ∧ b ≠ c ∧ c ≠ a :=
  ⟨h.isAdjacent.ne, h.cyclic.isAdjacent.ne, h.cyclic.cyclic.isAdjacent.ne⟩

theorem cross_rotate : ∀ {a b r : Orientation},
    IsAdjacent a b → cross (a.rotate r) (b.rotate r) = (cross a b).rotate r := by
  decide

theorem isAdjacent₃_rotate {a b c r : Orientation} :
    IsAdjacent₃ (a.rotate r) (b.rotate r) (c.rotate r) ↔ IsAdjacent₃ a b c := by
  constructor
  · rintro ⟨h, hr⟩
    have H := isAdjacent_rotate.1 h
    rw [cross_rotate H, rotate_inj] at hr
    exact ⟨H, hr⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h.rotate r, (cross_rotate h).symm⟩

theorem IsAdjacent₃.rotate {a b c : Orientation} (h : IsAdjacent₃ a b c) (r : Orientation) :
    IsAdjacent₃ (a.rotate r) (b.rotate r) (c.rotate r) :=
  isAdjacent₃_rotate.2 h

end Orientation
