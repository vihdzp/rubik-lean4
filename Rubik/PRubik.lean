import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Units
import Rubik.Piece

/-!
Defines the type of "pre-Rubik's cubes". Thes are all possible Rubik's cubes that can be assembled
by using the 8 availble edges and 12 available corners. In particular, there is no regard for
solvability, and "impossible" positions like a flipped edge or rotated corner are allowed.

We define a group structure in `PRubik`, and define the "Rubik's cube invariant", a surjective group
homomorphism into `ℤ₂ × ℤ₂ × ℤ₃` whose kernel will be shown to consist of precisely the solvable
Rubik's cubes.
-/

/-- The map `1 → 0`, `-1 → 1`. -/
def Units.toZMod (x : ℤˣ) : ZMod 2 :=
  if x = 1 then 0 else 1

@[simp]
theorem Units.toZMod_mul : ∀ x y : ℤˣ, (x * y).toZMod = x.toZMod + y.toZMod := by
  decide

theorem ZMod.cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by
  decide

open Orientation Equiv

/-- A pre-Rubik's cube. We represent this as a permutation of the edge pieces, and a permutation of
the corner pieces, such that pieces in the same edge or corner get mapped to the same edge or
corner.

This can be thought as the type of Rubik's cubes that can be physically assembled, without regard
for the solvability invariants. -/
structure PRubik : Type where
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm EdgePiece
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : EdgePiece) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic

attribute [simp] PRubik.edge_flip PRubik.corner_cyclic

namespace PRubik

deriving instance Fintype for PRubik

theorem edge_flip' (cube : PRubik) (e : EdgePiece) :
    cube.edgePieceEquiv e = (cube.edgePieceEquiv e.flip).flip :=
  cube.edge_flip e.flip

theorem corner_cyclic' (cube : PRubik) (c : CornerPiece) :
    cube.cornerPieceEquiv c = (cube.cornerPieceEquiv c.cyclic.cyclic).cyclic :=
  cube.corner_cyclic c.cyclic.cyclic

@[ext]
theorem ext (cube₁ cube₂ : PRubik)
    (he : ∀ e, cube₁.edgePieceEquiv e = cube₂.edgePieceEquiv e)
    (hc : ∀ c, cube₁.cornerPieceEquiv c = cube₂.cornerPieceEquiv c) :
    cube₁ = cube₂ := by
  obtain ⟨e₁, c₁, _, _⟩ := cube₁
  obtain ⟨e₂, c₂, _, _⟩ := cube₂
  simp
  rw [Equiv.ext_iff, Equiv.ext_iff]
  exact ⟨he, hc⟩

instance decEq : DecidableEq PRubik :=
  fun _ _ ↦ decidable_of_iff _ PRubik.ext_iff.symm

/-- An auxiliary function to get an edge piece in a cube, inferring the adjacency hypothesis. -/
def edgePiece (cube : PRubik) (a b : Orientation) (h : IsAdjacent a b := by decide) : EdgePiece :=
  cube.edgePieceEquiv ⟨a, b, h⟩

/-- An auxiliary function to get a corner piece in a cube, inferring the adjacency hypothesis. -/
def cornerPiece (cube : PRubik) (a b c : Orientation) (h : IsAdjacent₃ a b c := by decide) :
    CornerPiece :=
  cube.cornerPieceEquiv ⟨a, b, c, h⟩

/-- The solved Rubik's cube. -/
instance : One PRubik :=
  ⟨1, 1, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Inhabited PRubik := ⟨1⟩

@[simp]
theorem edgePieceEquiv_one : edgePieceEquiv 1 = 1 :=
  rfl

@[simp]
theorem cornerPieceEquiv_one : cornerPieceEquiv 1 = 1 :=
  rfl

/-- The solved Rubik's cube. -/
abbrev Solved : PRubik := 1

/-- The product of two Rubik's cubes is the Rubik's cube where the first's scramble is performed
before the second's.

This matches multiplication on `Equiv.Perm`, rather than the usual convention for functions. -/
instance : Mul PRubik :=
  ⟨fun cube₁ cube₂ ↦ by
    refine ⟨cube₁.edgePieceEquiv * cube₂.edgePieceEquiv,
      cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv, fun e ↦ ?_, fun c ↦ ?_⟩
    · dsimp
      rw [cube₂.edge_flip, cube₁.edge_flip]
    · dsimp
      rw [cube₂.corner_cyclic, cube₁.corner_cyclic]⟩

@[simp]
theorem edgePieceEquiv_mul (cube₁ cube₂ : PRubik) :
    (cube₁ * cube₂).edgePieceEquiv = cube₁.edgePieceEquiv * cube₂.edgePieceEquiv :=
  rfl

@[simp]
theorem cornerPieceEquiv_mul (cube₁ cube₂ : PRubik) :
    (cube₁ * cube₂).cornerPieceEquiv = cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv :=
  rfl

@[simp]
theorem edge_flip_inv (cube : PRubik) (e : EdgePiece) :
    cube.edgePieceEquiv⁻¹ e.flip = (cube.edgePieceEquiv⁻¹ e).flip := by
  conv_rhs => rw [← cube.edgePieceEquiv.inv_apply_self (EdgePiece.flip _)]
  rw [cube.edge_flip, Perm.apply_inv_self]

@[simp]
theorem corner_cyclic_inv (cube : PRubik) (c : CornerPiece) :
    cube.cornerPieceEquiv⁻¹ c.cyclic = (cube.cornerPieceEquiv⁻¹ c).cyclic := by
  conv_rhs => rw [← cube.cornerPieceEquiv.inv_apply_self (CornerPiece.cyclic _)]
  rw [cube.corner_cyclic, Perm.apply_inv_self]

theorem edgePieceEquiv_equiv (cube : PRubik) {e₁ e₂ : EdgePiece} (h : e₁ ≈ e₂) :
    cube.edgePieceEquiv e₁ ≈ cube.edgePieceEquiv e₂ := by
  obtain rfl | rfl := EdgePiece.equiv_iff.1 h
  · rfl
  · rw [edge_flip]
    exact EdgePiece.flip_equiv _

theorem cornerPieceEquiv_equiv (cube : PRubik) {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) :
    cube.cornerPieceEquiv c₁ ≈ cube.cornerPieceEquiv c₂ := by
  obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
  · rfl
  · rw [corner_cyclic]
    exact CornerPiece.cyclic_equiv _
  · rw [corner_cyclic]
    exact (CornerPiece.cyclic_equiv _).symm

/-- The inverse of a Rubik's cube is obtained by performing its moves backwards. -/
instance : Inv PRubik :=
  ⟨fun cube ↦ ⟨cube.edgePieceEquiv⁻¹, cube.cornerPieceEquiv⁻¹,
    cube.edge_flip_inv, cube.corner_cyclic_inv⟩⟩

@[simp]
theorem edgePieceEquiv_inv (cube : PRubik) : cube⁻¹.edgePieceEquiv = cube.edgePieceEquiv⁻¹ :=
  rfl

@[simp]
theorem cornerPieceEquiv_inv (cube : PRubik) : cube⁻¹.cornerPieceEquiv = cube.cornerPieceEquiv⁻¹ :=
  rfl

/-- The "pre-Rubik's cube" group. This isn't the true Rubik's cube group as it contains positions
that are unreachable by valid moves. -/
instance : Group PRubik where
  mul_assoc a b c := by ext <;> rfl
  one_mul a := by ext <;> rfl
  mul_one a := by ext <;> rfl
  inv_mul_cancel a := by ext <;> simp

/-- `edgePieceEquiv` as a monoid homomorphism. -/
@[simps]
def edgePieceEquivHom : PRubik →* Perm EdgePiece where
  toFun cube := cube.edgePieceEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `cornerPieceEquiv` as a monoid homomorphism. -/
@[simps]
def cornerPieceEquivHom : PRubik →* Perm CornerPiece where
  toFun cube := cube.cornerPieceEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A Rubik's cube defines a permutation of edges. -/
def edgeEquiv : PRubik →* Perm Edge where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.edgePieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.edgePieceEquiv)⁻¹ x⟧) ?_, fun e ↦ ?_, fun e ↦ ?_⟩
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl := EdgePiece.equiv_iff.1 h
      · rfl
      · rw [cube.edge_flip]
        exact EdgePiece.flip_equiv _
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl := EdgePiece.equiv_iff.1 h
      · rfl
      · rw [cube.edge_flip_inv]
        exact EdgePiece.flip_equiv _
    · refine Quotient.inductionOn e ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.inv_apply_self]
    · refine Quotient.inductionOn e ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.apply_inv_self]
  map_one' := by
    ext e
    refine Quotient.inductionOn e ?_
    exact fun _ ↦ rfl
  map_mul' cube₁ cube₂ := by
    ext e
    refine Quotient.inductionOn e ?_
    simp

theorem edgeEquiv_mk (cube : PRubik) (e : EdgePiece) :
    edgeEquiv cube ⟦e⟧ = ⟦cube.edgePieceEquiv e⟧ :=
  rfl

theorem edgeEquiv_one : edgeEquiv 1 = 1 :=
  map_one _

theorem edgeEquiv_of_edgePieceEquiv_eq_one (h : edgePieceEquiv cube = 1) : edgeEquiv cube = 1 := by
  ext e
  refine e.inductionOn ?_
  simp [edgeEquiv_mk, h]

/-- A Rubik's cube defines a permutation of corners. -/
def cornerEquiv : PRubik →* Perm Corner where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.cornerPieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.cornerPieceEquiv)⁻¹ x⟧) ?_, fun c ↦ ?_, fun c ↦ ?_⟩
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
      · rfl
      · rw [cube.corner_cyclic]
        exact CornerPiece.cyclic_equiv _
      · rw [cube.corner_cyclic]
        exact (CornerPiece.cyclic_equiv _).symm
    · intro e₁ e₂ h
      apply Quotient.sound
      obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
      · rfl
      · rw [cube.corner_cyclic_inv]
        exact CornerPiece.cyclic_equiv _
      · rw [cube.corner_cyclic_inv]
        exact (CornerPiece.cyclic_equiv _).symm
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.inv_apply_self]
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.apply_inv_self]
  map_one' := by
    ext e
    refine Quotient.inductionOn e ?_
    exact fun _ ↦ rfl
  map_mul' cube₁ cube₂ := by
    ext e
    refine Quotient.inductionOn e ?_
    simp

theorem cornerEquiv_mk (cube : PRubik) (c : CornerPiece) :
    cornerEquiv cube ⟦c⟧ = ⟦cube.cornerPieceEquiv c⟧ :=
  rfl

theorem cornerEquiv_one : cornerEquiv 1 = 1 :=
  map_one _

theorem cornerEquiv_of_cornerPieceEquiv_eq_one (h : cornerPieceEquiv cube = 1) :
    cornerEquiv cube = 1 := by
  ext c
  refine c.inductionOn ?_
  simp [cornerEquiv_mk, h]

/-- In a Rubik's cube where all edges are in their correct position, the "edge value" of an edge
represents whether it's flipped or not. -/
def edgeValue (cube : PRubik) (e : Edge) : ℤˣ :=
  e.lift (fun e ↦ if cube.edgePieceEquiv e = e then 1 else -1) (by
    intro e₁ e₂ h
    obtain rfl | rfl := EdgePiece.equiv_iff.1 h <;> simp
  )

theorem edgeValue_mk (cube : PRubik) (e : EdgePiece) :
    edgeValue cube ⟦e⟧ = if cube.edgePieceEquiv e = e then 1 else -1 :=
  rfl

theorem edgeValue_eq_one {cube : PRubik} {e : EdgePiece} :
    edgeValue cube ⟦e⟧ = 1 ↔ cube.edgePieceEquiv e = e := by
  simp [edgeValue_mk]

theorem edgeValue_eq_neg_one' {cube : PRubik} {e : EdgePiece} :
    edgeValue cube ⟦e⟧ = -1 ↔ cube.edgePieceEquiv e ≠ e := by
  simp [edgeValue_mk]

theorem edgeValue_eq_neg_one (he : edgeEquiv cube = 1) {e : EdgePiece} :
    edgeValue cube ⟦e⟧ = -1 ↔ cube.edgePieceEquiv e = e.flip := by
  rw [edgeValue_eq_neg_one']
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ e.flip_ne⟩
  have : ⟦cube.edgePieceEquiv e⟧ = (⟦e⟧ : Edge) := by rw [← edgeEquiv_mk, he, Perm.one_apply]
  rw [Quotient.eq, EdgePiece.equiv_iff] at this
  obtain he | he := this
  · contradiction
  · rw [he]

theorem edgeValue_mul (he₁ : edgeEquiv cube₁ = 1) (he₂ : edgeEquiv cube₂ = 1) (e : Edge) :
    edgeValue (cube₁ * cube₂) e = edgeValue cube₁ e * edgeValue cube₂ e := by
  have he₃ : edgeEquiv (cube₁ * cube₂) = 1 := by rw [map_mul, he₁, he₂, one_mul]
  refine e.inductionOn ?_
  intro e
  obtain h₁ | h₁ := Int.units_eq_one_or (edgeValue cube₁ ⟦e⟧) <;>
  obtain h₂ | h₂ := Int.units_eq_one_or (edgeValue cube₂ ⟦e⟧) <;>
  rw [h₁, h₂] <;>
  simp only [edgeValue_eq_one, edgeValue_eq_neg_one he₁, edgeValue_eq_neg_one he₂] at h₁ h₂ <;>
  simp [edgeValue_eq_one, edgeValue_eq_neg_one he₃, h₁, h₂]

/-- In a Rubik's cube where all corners are in their correct position, the "corner value" of a
corner represents the number of **counterclockwise** turns required to solve it. -/
def cornerValue (cube : PRubik) (c : Corner) : ZMod 3 :=
  c.lift (fun c ↦ (cornerPieceEquiv cube c).value Axis.x - c.value Axis.x) (by
    intro c₁ c₂ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;> simp
  )

theorem cornerValue_mk (cube : PRubik) (c : CornerPiece) :
    cornerValue cube ⟦c⟧ = (cornerPieceEquiv cube c).value Axis.x - c.value Axis.x :=
  rfl

theorem cornerValue_eq_zero (hc : cornerEquiv cube = 1) {c : CornerPiece} :
    cornerValue cube ⟦c⟧ = 0 ↔ cube.cornerPieceEquiv c = c := by
  rw [cornerValue_mk, sub_eq_zero, CornerPiece.value_eq_iff_of_equiv, eq_comm]
  rw [← Quotient.eq, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_eq_one (hc : cornerEquiv cube = 1) {c : CornerPiece} :
    cornerValue cube ⟦c⟧ = 1 ↔ cube.cornerPieceEquiv c = c.cyclic := by
  have : (1 + (1 + 1) : ZMod 3) = 0 := rfl
  rw [cornerValue_mk, CornerPiece.value_cyclic', CornerPiece.value_cyclic', sub_eq_iff_eq_add,
    add_comm, ← sub_eq_iff_eq_add, sub_sub, sub_sub, this, sub_zero,
    CornerPiece.value_eq_iff_of_equiv, ← CornerPiece.cyclic_inj, CornerPiece.cyclic₃]
  rw [← Quotient.eq, Corner.mk_cyclic, Corner.mk_cyclic, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_eq_two (hc : cornerEquiv cube = 1) {c : CornerPiece} :
    cornerValue cube ⟦c⟧ = 2 ↔ cube.cornerPieceEquiv c = c.cyclic.cyclic := by
  have : (2 + 1 : ZMod 3) = 0 := rfl
  rw [cornerValue_mk, sub_eq_iff_eq_add, CornerPiece.value_cyclic', add_comm, sub_eq_iff_eq_add,
    add_assoc, this, add_zero, CornerPiece.value_eq_iff_of_equiv,
    ← CornerPiece.cyclic_inj, ← CornerPiece.cyclic_inj, CornerPiece.cyclic₃]
  rw [← Quotient.eq, Corner.mk_cyclic, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_mul (hc₁ : cornerEquiv cube₁ = 1) (hc₂ : cornerEquiv cube₂ = 1) (c : Corner) :
    cornerValue (cube₁ * cube₂) c = cornerValue cube₁ c + cornerValue cube₂ c := by
  have hc₃ : cornerEquiv (cube₁ * cube₂) = 1 := by rw [map_mul, hc₁, hc₂, one_mul]
  have H₁ : (1 + 1 : ZMod 3) = 2 := rfl
  have H₂ : (1 + 2 : ZMod 3) = 0 := rfl
  have H₃ : (2 + 1 : ZMod 3) = 0 := rfl
  have H₄ : (2 + 2 : ZMod 3) = 1 := rfl
  refine c.inductionOn ?_
  intro c
  obtain h₁ | h₁ | h₁ := ZMod.cases (cube₁.cornerValue ⟦c⟧) <;>
  obtain h₂ | h₂ | h₂ := ZMod.cases (cube₂.cornerValue ⟦c⟧) <;>
  rw [h₁, h₂] <;>
  simp only [cornerValue_eq_zero hc₁, cornerValue_eq_zero hc₂, cornerValue_eq_one hc₁,
    cornerValue_eq_one hc₂, cornerValue_eq_two hc₁, cornerValue_eq_two hc₂] at h₁ h₂ <;>
  simp [cornerValue_eq_zero hc₃, cornerValue_eq_one hc₃, cornerValue_eq_two hc₃, H₁, H₂, H₃, H₄,
    h₁, h₂]

/-- The total parity of a Rubik's cube is the combined parity of edge and corner permutations.

This is an invariant under any valid move. -/
def parity : PRubik →* ℤˣ :=
  Perm.sign.comp edgeEquiv * Perm.sign.comp cornerEquiv

/-- The Rubik's cube with a single edge swapped with its counterclockwise edge in the same face. -/
def swapEdges (h : IsAdjacent a b) : PRubik where
  edgePieceEquiv := (swap ⟨a, b, h⟩ ⟨a, cross a b, h.cross_left.symm⟩).trans
    (swap ⟨b, a, h.symm⟩ ⟨cross a b, a, h.cross_left⟩)
  cornerPieceEquiv := 1
  edge_flip := by
    revert a b
    decide
  corner_cyclic _ := rfl

@[simp]
theorem parity_swapEdges : ∀ {a b} (h : IsAdjacent a b), parity (swapEdges h) = -1 := by
  decide

/-- The parity of flipped edges in a Rubik's cube can be measured as the parity of the edge piece
permutation.

This is an invariant under any valid move. -/
def edgeFlip : PRubik →* ℤˣ :=
  Perm.sign.comp edgePieceEquivHom

/-- Flips a single edge. -/
def flipEdge (e : Edge) : PRubik where
  edgePieceEquiv := e.flipEquiv
  cornerPieceEquiv := 1
  edge_flip a := e.flipEquiv_flip a
  corner_cyclic _ := rfl

@[simp]
theorem edgePieceEquiv_flipEdge (e : Edge) : edgePieceEquiv (flipEdge e) = e.flipEquiv :=
  rfl

@[simp]
theorem cornerPieceEquiv_flipEdge (e : Edge) : cornerPieceEquiv (flipEdge e) = 1 :=
  rfl

@[simp]
theorem edgeFlip_flipEdge : ∀ e, edgeFlip (flipEdge e) = -1 := by
  decide

theorem cornerPieceEquiv_value (cube : PRubik) (c : CornerPiece) (a : Axis) :
    (cube.cornerPieceEquiv c).value a =
    (cube.cornerPieceEquiv (c.withAxis a)).value a + c.value a := by
  obtain h | h | h := CornerPiece.equiv_iff.1 (CornerPiece.withAxis_equiv c a)
  · rw [h]
    conv_rhs => right; rw [← h]
    rw [CornerPiece.value_withAxis, add_zero]
  · rw [h, corner_cyclic, CornerPiece.value_cyclic, add_assoc, self_eq_add_right,
      CornerPiece.value_of_snd]
    · rfl
    · rw [← c.cyclic₃, ← h]
      simp
  · conv_lhs => rw [← h]
    rw [corner_cyclic, CornerPiece.value_cyclic, add_right_inj, CornerPiece.value_of_thd]
    rw [← h]
    simp

private theorem cornerRotationAux (cube₁ cube₂ : PRubik) (c : Corner) (a : Axis) :
    (cube₁.cornerPieceEquiv (cube₂.cornerPieceEquiv (c.toCornerPiece a))).value a
    = (cube₁.cornerPieceEquiv ((cornerEquiv cube₂ c).toCornerPiece a)).value a
    + (cube₂.cornerPieceEquiv (c.toCornerPiece a)).value a := by
  refine Quotient.inductionOn c ?_
  intro c
  dsimp [cornerEquiv_mk]
  conv_lhs => rw [cornerPieceEquiv_value]
  rw [add_left_inj, CornerPiece.withAxis_eq_of_equiv]
  exact cornerPieceEquiv_equiv _ (c.withAxis_equiv a)

/-- To calculate the amount of corner rotation mod 3, we fix an arbitrary axis (here the X axis) and
count the number of **counterclockwise** corner rotations needed to orient the pieces of the
corresponding axis to said axis.

This is an invariant under any valid move. -/
def cornerRotation : PRubik →* Multiplicative (ZMod 3) where
  toFun cube := ∏ c : Corner,
    (Multiplicative.ofAdd <| (cube.cornerPieceEquiv (c.toCornerPiece Axis.x)).value Axis.x)
  map_one' := by
    convert Finset.prod_const_one
    simp
  map_mul' cube₁ cube₂ := by
    dsimp
    simp_rw [cornerRotationAux, ofAdd_add, Finset.prod_mul_distrib, mul_left_inj]
    rw [Finset.prod_equiv (cornerEquiv cube₂)] <;>
    simp

/-- Rotates a single corner **clockwise**. -/
def rotateCorner (c : Corner) : PRubik where
  edgePieceEquiv := 1
  cornerPieceEquiv := c.rotateEquiv
  edge_flip _ := rfl
  corner_cyclic := c.rotateEquiv_cyclic

@[simp]
theorem edgePieceEquiv_rotateCorner (c : Corner) : edgePieceEquiv (rotateCorner c) = 1 :=
  rfl

theorem cornerPieceEquiv_rotateCorner (c : Corner) :
    cornerPieceEquiv (rotateCorner c) = c.rotateEquiv :=
  rfl

@[simp]
theorem cornerPieceEquiv_rotateCorner_self (c : CornerPiece) :
    cornerPieceEquiv (rotateCorner ⟦c⟧) c = c.cyclic := by
  rw [cornerPieceEquiv_rotateCorner, Corner.rotateEquiv_self]

@[simp]
theorem cornerPieceEquiv_rotateCorner_inv_self (c : CornerPiece) :
    (cornerPieceEquiv (rotateCorner ⟦c⟧))⁻¹ c = c.cyclic.cyclic := by
  rw [cornerPieceEquiv_rotateCorner, Corner.rotateEquiv_inv_self]

@[simp]
theorem cornerRotation_rotateCorner :
    ∀ c, cornerRotation (rotateCorner c) = Multiplicative.ofAdd 1 := by
  decide

/-- The **Rubik's cube invariant**. This is the combined `parity`, `edgeFlip`, and `cornerRotation`
of a Rubik's cube.

A Rubik's cube is solvable iff it lies in the kernel of this homomorphism. -/
def invariant : PRubik →* ℤˣ × ℤˣ × Multiplicative (ZMod 3) :=
  parity.prod <| edgeFlip.prod cornerRotation

/-- A constructive right inverse for the invariant. -/
def invariant_inv : ℤˣ × ℤˣ × Multiplicative (ZMod 3) → PRubik :=
  fun ⟨a, b, c⟩ ↦ (swapEdges (default : EdgePiece).isAdjacent) ^ ((1 - a.1) / 2) *
    (flipEdge default) ^ b.toZMod.1 * (rotateCorner default) ^ c.1

theorem invariant_rightInverse : Function.RightInverse invariant_inv invariant := by
  decide

theorem invariant_surjective : Function.Surjective invariant :=
  invariant_rightInverse.surjective

/-- A Rubik's cube is valid when it has invariant 1. We show that this condition is equivalent to
being solvable. -/
def IsValid (cube : PRubik) : Prop :=
  cube ∈ invariant.ker

instance : DecidablePred IsValid :=
  fun cube ↦ inferInstanceAs (Decidable (invariant cube = 1))

theorem isValid_one : IsValid 1 :=
  one_mem _

theorem IsValid.mul (h₁ : IsValid cube₁) (h₂ : IsValid cube₂) : IsValid (cube₁ * cube₂) :=
  mul_mem h₁ h₂

theorem IsValid.inv (h : IsValid cube) : IsValid cube⁻¹ :=
  inv_mem h

theorem isValid_iff :
    IsValid cube ↔ parity cube = 1 ∧ edgeFlip cube = 1 ∧ cornerRotation cube = 1 := by
  rw [IsValid, invariant]
  simp only [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]

theorem IsValid.parity (h : IsValid cube) : parity cube = 1 :=
  (isValid_iff.1 h).1

theorem IsValid.edgeFlip (h : IsValid cube) : edgeFlip cube = 1 :=
  (isValid_iff.1 h).2.1

theorem IsValid.cornerRotation (h : IsValid cube) : cornerRotation cube = 1 :=
  (isValid_iff.1 h).2.2

end PRubik

/-- The subgroup of valid Rubik's cubes, i.e. those that can be reached using only valid moves. -/
def Rubik : Subgroup PRubik :=
  PRubik.invariant.ker

namespace Rubik

instance : Fintype Rubik :=
  Subtype.fintype PRubik.IsValid

/-- Construct a Rubik's cube, inferring the validity hypothesis. -/
def mk (cube : PRubik) (h : PRubik.IsValid cube := by decide) : Rubik :=
  ⟨cube, h⟩

theorem isValid (cube : Rubik) : cube.val.IsValid :=
  cube.2

end Rubik
