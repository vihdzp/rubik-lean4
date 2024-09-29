# Rubik's cubes in Lean

This repository provides a mathematical formalization of Rubik's cubes. We prove the following results:

- `PRubik.isSolvable_iff_isValid`: a Rubik's cube is solvable iff it is "valid", i.e. it has no flipped edges, swapped pieces, or rotated corners.
- `Rubik.card`: there are 2¹² × 3⁸ × 8! × 11 = 43,252,003,274,489,856,000 solvable Rubik's cubes.

We also provide `Stickers.toRubik`, which assembles a Rubik's cube from its stickers and automatically deduces its validity.

## Implementation

Our most basic types are `Axis` and `Orientation`, which abstract the geometry of 3D space. An orientation represents one of six axis-aligned directions - as such, it can also be used to represent one of the six colors of the stickers.

An `EdgePiece` consists of two orientations with distinct axes. Since orientations represent both position and colors, an `EdgePiece` can dually represent a particular edge sticker, or a particular position for it. Similarly, a `CornerPiece` consists of three orientations with pairwise distinct axes, and it can represent a particular corner sticker, or a position for it.

A `PRubik` or "pre-Rubik's cube" consists of a `Perm EdgePiece` and a `Perm CornerPiece`, which are to be interpreted as returning the given sticker color at any given position. These functions are subject to the conditions that edge pieces in the same edge are mapped to edge pieces in the same edge, and likewise for corner pieces. There is no solvability requirement. We can define a group structure on `PRubik` by simply multiplying the corresponding permutations together. We define three group homomorphisms `edgeFlip`, `parity`, and `cornerRotation`, which combine to form the Rubik's cube invariant. A `PRubik` is said to be valid when it lies in the kernel of this homomorphism, and `Rubik` is the subtype which corresponds to this kernel.

Each orientation can be assigned a particular `PRubik.ofOrientation` which corresponds to turning that face. A list of `Orientation` can be performed as `Moves`, and we say that a `PRubik` is solvable when it can be assembled from the solved state from such a sequence.

## Other project ideas

There are various possible ways this project could be expanded upon or generalized:

- Solving smaller (2 × 2 × 2) or larger Rubik's cubes 
- Solving other twisty puzzles, like the megaminx, pyraminx, ...
- Solving higher-dimensional Rubik's cubes
