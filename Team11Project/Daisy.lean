import Rubik
import Mathlib.Tactic.Group

/-!
# Daisy algorithm — Phase 1 of solving the cube

Specification: see `Team11Project/Daisy.md`. This file formalizes the algorithm
that places the four white edge stickers around the yellow center, producing a
"daisy" on top of the cube (white at U2, U4, U6, U8).

Implementation strategy: we exploit the cube's y-rotation symmetry. Instead of
hardcoding 20 case sequences, we define the F-face base algorithm only and
derive the other three U-slot variants by applying a y-rotation. The 20
per-case lemmas reduce to:
  * 5 F-base per-case lemmas (proved by `decide`),
  * 1 symmetry meta-lemma (proved by induction with a small `decide` base),
  * mechanical derivation of the rest.

The y-rotation cycles `F → R → B → L → F` with `U`, `D` fixed.

Conventions:
* The library colors `U = white` and `D = yellow`
  (see `.lake/packages/Rubik/Rubik/Orientation.lean` lines 150–157).
* `c.edgePieceEquiv` is *passive*: `c.edgePieceEquiv e` is the original
  sticker-label currently at position `e`.
* `*` on `PRubik` composes left-to-right (`c * move m` = "apply m to c"),
  but `*` on `Equiv.Perm` is right-to-left (`(f * g) x = f (g x)`).
* The library has no wide moves, no slice moves, no whole-cube rotations.
  Where the spec calls for "rotate cube" and "perform d", we instead enumerate
  the four U-edge slots directly with y-rotated copies of the F-face case
  algorithm.

Numbering scheme from `Daisy.md`:
```
         U1 U2 U3            (U2 = mk' U B,  U4 = mk' U L,
         U4 U5 U6             U6 = mk' U R,  U8 = mk' U F)
         U7 U8 U9
L1 L2 L3 F1 F2 F3 R1 R2 R3   (F2 = mk' F U,  F6 = mk' F R,
L4 L5 L6 F4 F5 F6 R4 R5 R6    F8 = mk' F D,  R4 = mk' R F)
L7 L8 L9 F7 F8 F9 R7 R8 R9
         D1 D2 D3            (D2 = mk' D F)
         D4 D5 D6
         D7 D8 D9
```
-/

namespace Daisy

open Orientation PRubik

/-! ## The y-rotation on faces -/

/-- `σ` is the y-rotation: cycles `F → R → B → L → F`, fixes `U`, `D`. -/
def σ : Orientation → Orientation
  | .U => .U
  | .D => .D
  | .F => .R
  | .R => .B
  | .B => .L
  | .L => .F

/-- Inverse y-rotation: cycles `F → L → B → R → F`. -/
def σInv : Orientation → Orientation
  | .U => .U
  | .D => .D
  | .F => .L
  | .L => .B
  | .B => .R
  | .R => .F

@[simp] theorem σ_σInv : ∀ o, σ (σInv o) = o := by decide
@[simp] theorem σInv_σ : ∀ o, σInv (σ o) = o := by decide

/-- `σ` as an `Equiv`. -/
def σEquiv : Equiv.Perm Orientation where
  toFun := σ
  invFun := σInv
  left_inv := σInv_σ
  right_inv := σ_σInv

/-! ## The y-rotation lifted to `EdgePiece` -/

theorem σ_isAdjacent {a b : Orientation} (h : IsAdjacent a b) : IsAdjacent (σ a) (σ b) := by
  revert h
  revert a b
  decide

theorem σInv_isAdjacent {a b : Orientation} (h : IsAdjacent a b) :
    IsAdjacent (σInv a) (σInv b) := by
  revert h
  revert a b
  decide

/-- Lift `σ` to an EdgePiece map by relabeling both `fst` and `snd`. -/
def ρFun (e : EdgePiece) : EdgePiece :=
  ⟨σ e.fst, σ e.snd, σ_isAdjacent e.isAdjacent⟩

/-- Inverse lift. -/
def ρInvFun (e : EdgePiece) : EdgePiece :=
  ⟨σInv e.fst, σInv e.snd, σInv_isAdjacent e.isAdjacent⟩

@[simp] theorem ρFun_ρInvFun (e : EdgePiece) : ρFun (ρInvFun e) = e := by
  cases e with
  | mk a b h => simp [ρFun, ρInvFun]

@[simp] theorem ρInvFun_ρFun (e : EdgePiece) : ρInvFun (ρFun e) = e := by
  cases e with
  | mk a b h => simp [ρFun, ρInvFun]

/-- `ρ` is the y-rotation as a permutation of EdgePiece. -/
def ρ : Equiv.Perm EdgePiece where
  toFun := ρFun
  invFun := ρInvFun
  left_inv := ρInvFun_ρFun
  right_inv := ρFun_ρInvFun

@[simp] theorem ρ_apply (e : EdgePiece) : ρ e = ρFun e := rfl
@[simp] theorem ρ_symm_apply (e : EdgePiece) : ρ.symm e = ρInvFun e := rfl

/-! ## Lifting σ to move sequences -/

/-- Apply `σ` to every face symbol in a move list. -/
def σM (m : Moves) : Moves := m.map σ

@[simp] theorem σM_nil : σM [] = [] := rfl
@[simp] theorem σM_cons (r : Orientation) (m : Moves) : σM (r :: m) = σ r :: σM m := rfl
@[simp] theorem σM_append (l m : Moves) : σM (l ++ m) = σM l ++ σM m := List.map_append _ _ _

/-! ## Symmetry meta-lemma

The cube has y-rotation symmetry: applying the rotated move list is the same
as conjugating by `ρ` on edges. -/

/-- Base case: a single face turn commutes with the y-rotation up to
conjugation by `ρ`. Proved by `decide` over the 6 face choices. -/
theorem ofOrientation_σ_edge (r : Orientation) :
    (ofOrientation (σ r)).edgePieceEquiv =
      ρ * (ofOrientation r).edgePieceEquiv * ρ⁻¹ := by
  -- Equivalence of permutations: check pointwise on the finite type EdgePiece.
  apply Equiv.ext
  intro e
  revert e r
  decide

/-- Symmetry meta-lemma: the edge permutation of any rotated move list equals
the conjugate of the original edge permutation by `ρ`. -/
theorem move_σM_edge (m : Moves) :
    (PRubik.move (σM m)).edgePieceEquiv =
      ρ * (PRubik.move m).edgePieceEquiv * ρ⁻¹ := by
  induction m with
  | nil =>
    simp [σM_nil, PRubik.move]
  | cons r m IH =>
    simp only [σM_cons, PRubik.move_cons, edgePieceEquiv_mul,
      ofOrientation_σ_edge r, IH]
    -- (ρ * Pr * ρ⁻¹) * (ρ * Pm * ρ⁻¹) = ρ * (Pr * Pm) * ρ⁻¹
    group

/-! ## Color predicate -/

/-- The sticker color now at position `e` in cube `c` is `U` (white). -/
def whiteAt (c : PRubik) (e : EdgePiece) : Prop :=
  (c.edgePieceEquiv e).fst = Orientation.U

instance (c : PRubik) (e : EdgePiece) : Decidable (whiteAt c e) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## The four U-edge target slots -/

inductive Slot where
  | UF | UR | UB | UL
  deriving DecidableEq, Repr, Fintype

/-- Number of times to apply σ for each slot (0 for UF, 1 for UR, etc.). -/
def Slot.idx : Slot → Nat
  | .UF => 0 | .UR => 1 | .UB => 2 | .UL => 3

/-! ## Case tags

The five cases from the spec, named after the position checked for the F-face
slot. -/

inductive CaseTag where
  | F2 | F6 | R4 | F8 | D2
  deriving DecidableEq, Repr, Fintype

/-! ## F-base algorithm

The five F-face-slot move sequences are taken **verbatim** from `Daisy.md`. The
other three slot variants are derived by iterating `σM` (which relabels face
symbols by the face-cycle `F → R → B → L → F`, with `U`, `D` fixed). -/

/-- F-face-slot move sequences, **verbatim** from `Daisy.md`. -/
def baseMoves : CaseTag → Moves
  | .F2 => Moves.F  ++ Moves.U' ++ Moves.R ++ Moves.U
  | .F6 => Moves.U' ++ Moves.R  ++ Moves.U
  | .R4 => Moves.F'
  | .F8 => Moves.F' ++ Moves.U' ++ Moves.R ++ Moves.U
  | .D2 => Moves.F2

/-- F-face-slot source positions. For each case tag, this is where a white
sticker currently must lie for the case algorithm to lift it into the F-face
slot. -/
def baseSource : CaseTag → EdgePiece
  | .F2 => EdgePiece.mk' F U  -- F2 sticker (F-side of U-F edge)
  | .F6 => EdgePiece.mk' F R  -- F6 sticker (F-side of F-R edge)
  | .R4 => EdgePiece.mk' R F  -- R4 sticker (R-side of F-R edge)
  | .F8 => EdgePiece.mk' F D  -- F8 sticker (F-side of D-F edge)
  | .D2 => EdgePiece.mk' D F  -- D2 sticker (D-side of D-F edge)

/-- The F-face target position (= U8 in the spec, = mk' U F). -/
def baseTarget : EdgePiece := EdgePiece.mk' U F

/-! ## Iteration helpers -/

/-- Apply σ to a face k times. -/
def σIter : Nat → Orientation → Orientation
  | 0, o => o
  | n + 1, o => σ (σIter n o)

/-- Apply σM to a move list k times. -/
def σMIter : Nat → Moves → Moves
  | 0, m => m
  | n + 1, m => σM (σMIter n m)

/-- Apply ρ to an EdgePiece k times. -/
def ρIter : Nat → EdgePiece → EdgePiece
  | 0, e => e
  | n + 1, e => ρFun (ρIter n e)

theorem σMIter_succ_apply (n : Nat) (m : Moves) : σMIter (n + 1) m = σM (σMIter n m) := rfl

/-! ## Per-slot, per-case definitions derived from the F-base

For each `(slot, case)` the source is where a white sticker currently must lie
for the case algorithm to lift it into the slot. The 20 entries partition the
20 non-U-target edge sticker positions. -/

/-- The U-side sticker position of the U-edge for each slot. -/
def Slot.target (s : Slot) : EdgePiece := ρIter s.idx baseTarget

def caseSource (s : Slot) (t : CaseTag) : EdgePiece := ρIter s.idx (baseSource t)
def caseMoves (s : Slot) (t : CaseTag) : Moves := σMIter s.idx (baseMoves t)

/-- The cube has the daisy pattern: white edge stickers on all four U-edge
positions (U2, U4, U6, U8 in the spec's numbering). -/
def daisyDone (c : PRubik) : Prop :=
  whiteAt c Slot.UF.target ∧ whiteAt c Slot.UR.target ∧
  whiteAt c Slot.UB.target ∧ whiteAt c Slot.UL.target

instance (c : PRubik) : Decidable (daisyDone c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Iterated symmetry -/

/-- Iterated form of the meta-lemma. -/
theorem move_σMIter_edge (k : Nat) (m : Moves) :
    (PRubik.move (σMIter k m)).edgePieceEquiv =
      (ρ ^ k) * (PRubik.move m).edgePieceEquiv * (ρ ^ k)⁻¹ := by
  induction k with
  | zero => simp [σMIter, pow_zero]
  | succ n IH =>
    rw [σMIter_succ_apply, move_σM_edge, IH, pow_succ']
    group

/-- `ρ^k` applied via `ρIter`. -/
theorem ρ_pow_apply (k : Nat) (e : EdgePiece) : (ρ ^ k) e = ρIter k e := by
  induction k with
  | zero => simp [ρIter, pow_zero]
  | succ n IH =>
    rw [pow_succ', Equiv.Perm.mul_apply, IH]
    rfl

/-! ## Per-case correctness lemmas

Each lemma asserts: applying `caseMoves slot tag` to the solved cube produces
a permutation that moves the source piece to the target. By multiplicativity
of `edgePieceEquiv`, this gives the soundness corollary
`whiteAt (c * π) target ↔ whiteAt c source` for *any* starting cube `c`. -/

/-! ### F-base per-case lemmas (5 × `decide`) -/

theorem baseMoves_target (t : CaseTag) :
    (PRubik.move (baseMoves t)).edgePieceEquiv baseTarget = baseSource t := by
  cases t <;> decide

/-! ### General per-case lemma derived from F-base + symmetry -/

theorem caseMoves_target (s : Slot) (t : CaseTag) :
    (PRubik.move (caseMoves s t)).edgePieceEquiv s.target = caseSource s t := by
  unfold caseMoves Slot.target caseSource
  set k := s.idx
  rw [show ρIter k baseTarget = (ρ ^ k) baseTarget from (ρ_pow_apply k baseTarget).symm]
  rw [show ρIter k (baseSource t) = (ρ ^ k) (baseSource t) from (ρ_pow_apply k (baseSource t)).symm]
  rw [move_σMIter_edge]
  -- Goal: (ρ^k * Pt * (ρ^k)⁻¹) ((ρ^k) baseTarget) = (ρ^k) (baseSource t)
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_apply_self]
  rw [baseMoves_target]

/-- Each case algorithm fixes the *other* three U-targets as the identity
permutation. Empirically verified: e.g. `F U' R U` maps each of `mk' U R`,
`mk' U B`, `mk' U L` to itself. -/
theorem caseMoves_preserves_others (s s' : Slot) (t : CaseTag) (h : s' ≠ s) :
    (PRubik.move (caseMoves s t)).edgePieceEquiv s'.target = s'.target := by
  revert h
  cases s <;> cases s' <;> cases t <;> decide

/-- Soundness of one case: if the source has white, then after the moves the
target has white. Holds for any cube `c`. -/
theorem whiteAt_after_caseMoves (c : PRubik) (s : Slot) (t : CaseTag)
    (hsrc : whiteAt c (caseSource s t)) :
    whiteAt (c * PRubik.move (caseMoves s t)) s.target := by
  unfold whiteAt
  rw [edgePieceEquiv_mul]
  show (c.edgePieceEquiv ((PRubik.move _).edgePieceEquiv s.target)).fst = _
  rw [caseMoves_target]
  exact hsrc

/-- Other-slot preservation as a soundness corollary. -/
theorem whiteAt_other_preserved (c : PRubik) (s s' : Slot) (t : CaseTag)
    (h : s' ≠ s) :
    whiteAt (c * PRubik.move (caseMoves s t)) s'.target ↔ whiteAt c s'.target := by
  unfold whiteAt
  rw [edgePieceEquiv_mul]
  show (c.edgePieceEquiv ((PRubik.move _).edgePieceEquiv s'.target)).fst = _ ↔ _
  rw [caseMoves_preserves_others s s' t h]

/-! ## The fixup function -/

/-- Try to fix one specific U-slot. Returns `none` if the slot is already
white, or if no candidate source has white. Otherwise returns the moves of
the first matching case (in order F2, F6, R4, F8, D2). -/
def tryFixupSlot (c : PRubik) (s : Slot) : Option Moves :=
  if whiteAt c s.target then none
  else if whiteAt c (caseSource s .F2) then some (caseMoves s .F2)
  else if whiteAt c (caseSource s .F6) then some (caseMoves s .F6)
  else if whiteAt c (caseSource s .R4) then some (caseMoves s .R4)
  else if whiteAt c (caseSource s .F8) then some (caseMoves s .F8)
  else if whiteAt c (caseSource s .D2) then some (caseMoves s .D2)
  else none

/-- Try to find some U-slot we can fix. Iterates through `UF, UR, UB, UL`. -/
def tryAnyFixupOpt (c : PRubik) : Option Moves :=
  match tryFixupSlot c .UF with
  | some m => some m
  | none =>
    match tryFixupSlot c .UR with
    | some m => some m
    | none =>
      match tryFixupSlot c .UB with
      | some m => some m
      | none => tryFixupSlot c .UL

/-- Try the fixup after `k` clockwise U-rotations are applied to `c`. The
returned moves include the leading `U^k`. Required because some misplaced
white edges sit in middle/D positions whose "natural" target slot is already
white; rotating the U layer cycles a non-white slot to the right place. -/
def tryFixupWithUk (c : PRubik) (k : Nat) : Option Moves :=
  let pre := List.replicate k Orientation.U
  let cRot := c * PRubik.move pre
  (tryAnyFixupOpt cRot).map (pre ++ ·)

/-- Try `k = 0, 1, 2, 3`. Returns `[]` only when daisy is already done (after
4 U-rotations the cube returns to its original state, so if no slot fires in
any rotation, no slot can fire at all). -/
def tryAnyFixup (c : PRubik) : Moves :=
  (tryFixupWithUk c 0).getD <|
    (tryFixupWithUk c 1).getD <|
      (tryFixupWithUk c 2).getD <|
        (tryFixupWithUk c 3).getD []

/-! ## The Daisy algorithm

Bounded loop of exactly four iterations. Four is sufficient because each
iteration fills at least one previously-empty U-slot, and there are only
four U-slots. -/

def daisyMoves (c : PRubik) : Moves :=
  let m1 := tryAnyFixup c
  let c1 := c * PRubik.move m1
  let m2 := tryAnyFixup c1
  let c2 := c1 * PRubik.move m2
  let m3 := tryAnyFixup c2
  let c3 := c2 * PRubik.move m3
  let m4 := tryAnyFixup c3
  m1 ++ m2 ++ m3 ++ m4

/-! ## Counting white U-targets and U-rotation invariance -/

/-- Number of slots whose target currently shows a white sticker. -/
def numWhiteUTargets (c : PRubik) : Nat :=
  (if whiteAt c Slot.UF.target then 1 else 0) +
  (if whiteAt c Slot.UR.target then 1 else 0) +
  (if whiteAt c Slot.UB.target then 1 else 0) +
  (if whiteAt c Slot.UL.target then 1 else 0)

theorem daisyDone_iff_count (c : PRubik) :
    daisyDone c ↔ numWhiteUTargets c = 4 := by
  unfold daisyDone numWhiteUTargets
  by_cases h1 : whiteAt c Slot.UF.target <;>
  by_cases h2 : whiteAt c Slot.UR.target <;>
  by_cases h3 : whiteAt c Slot.UB.target <;>
  by_cases h4 : whiteAt c Slot.UL.target <;>
  simp [h1, h2, h3, h4]

/-- The U-rotation cycles slot targets: UF → UR → UB → UL → UF. -/
def Slot.uNext : Slot → Slot
  | .UF => .UR | .UR => .UB | .UB => .UL | .UL => .UF

theorem ofOrientation_U_slot (s : Slot) :
    (PRubik.ofOrientation Orientation.U).edgePieceEquiv s.target = s.uNext.target := by
  cases s <;> decide

theorem whiteAt_U_cycle (c : PRubik) (s : Slot) :
    whiteAt (c * PRubik.ofOrientation Orientation.U) s.target ↔
      whiteAt c s.uNext.target := by
  unfold whiteAt
  rw [edgePieceEquiv_mul]
  show (c.edgePieceEquiv ((PRubik.ofOrientation _).edgePieceEquiv s.target)).fst = _ ↔ _
  rw [ofOrientation_U_slot]

theorem numWhiteUTargets_U (c : PRubik) :
    numWhiteUTargets (c * PRubik.ofOrientation Orientation.U) = numWhiteUTargets c := by
  unfold numWhiteUTargets
  have h1 := whiteAt_U_cycle c .UF
  have h2 := whiteAt_U_cycle c .UR
  have h3 := whiteAt_U_cycle c .UB
  have h4 := whiteAt_U_cycle c .UL
  simp only [Slot.uNext] at h1 h2 h3 h4
  by_cases hUF : whiteAt c Slot.UF.target <;>
  by_cases hUR : whiteAt c Slot.UR.target <;>
  by_cases hUB : whiteAt c Slot.UB.target <;>
  by_cases hUL : whiteAt c Slot.UL.target <;>
  simp [hUF, hUR, hUB, hUL, h1, h2, h3, h4]

theorem move_singleton (r : Orientation) :
    PRubik.move [r] = PRubik.ofOrientation r := by
  show PRubik.move (r :: []) = _
  rw [PRubik.move_cons, PRubik.move_nil, mul_one]

theorem numWhiteUTargets_Uk (c : PRubik) (k : Nat) :
    numWhiteUTargets (c * PRubik.move (List.replicate k Orientation.U)) =
      numWhiteUTargets c := by
  revert c
  induction k with
  | zero => intro c; simp
  | succ n IH =>
    intro c
    rw [List.replicate_succ, ← List.singleton_append, PRubik.move_append,
      ← mul_assoc, move_singleton, IH (c * PRubik.ofOrientation Orientation.U)]
    exact numWhiteUTargets_U c

/-! ## Step lemma: each successful fixup increases the count by 1 -/

/-- Helper: for a chosen `(s, t)`, if target is non-white and source is white,
then the case-application increases count by 1. Combines target gain and
other-slot preservation. -/
theorem caseMoves_count_progress (c : PRubik) (s : Slot) (t : CaseTag)
    (htgt : ¬ whiteAt c s.target) (hsrc : whiteAt c (caseSource s t)) :
    numWhiteUTargets (c * PRubik.move (caseMoves s t)) = numWhiteUTargets c + 1 := by
  -- After the move:
  --   target s   becomes white (gain)
  --   each s' ≠ s preserves its whiteness (preservation)
  have htgtAfter : whiteAt (c * PRubik.move (caseMoves s t)) s.target :=
    whiteAt_after_caseMoves c s t hsrc
  -- For each other slot s', the iff
  have hUF : s ≠ Slot.UF →
      (whiteAt (c * PRubik.move (caseMoves s t)) Slot.UF.target ↔
        whiteAt c Slot.UF.target) := fun h => whiteAt_other_preserved c s _ t h.symm
  have hUR : s ≠ Slot.UR →
      (whiteAt (c * PRubik.move (caseMoves s t)) Slot.UR.target ↔
        whiteAt c Slot.UR.target) := fun h => whiteAt_other_preserved c s _ t h.symm
  have hUB : s ≠ Slot.UB →
      (whiteAt (c * PRubik.move (caseMoves s t)) Slot.UB.target ↔
        whiteAt c Slot.UB.target) := fun h => whiteAt_other_preserved c s _ t h.symm
  have hUL : s ≠ Slot.UL →
      (whiteAt (c * PRubik.move (caseMoves s t)) Slot.UL.target ↔
        whiteAt c Slot.UL.target) := fun h => whiteAt_other_preserved c s _ t h.symm
  -- Now case-split on s and unfold numWhiteUTargets
  unfold numWhiteUTargets
  cases s
  all_goals (
    first
    | (have e1 := hUR (by decide); have e2 := hUB (by decide); have e3 := hUL (by decide)
       simp [htgt, htgtAfter, e1, e2, e3]; try omega)
    | (have e1 := hUF (by decide); have e2 := hUB (by decide); have e3 := hUL (by decide)
       simp [htgt, htgtAfter, e1, e2, e3]; try omega)
    | (have e1 := hUF (by decide); have e2 := hUR (by decide); have e3 := hUL (by decide)
       simp [htgt, htgtAfter, e1, e2, e3]; try omega)
    | (have e1 := hUF (by decide); have e2 := hUR (by decide); have e3 := hUB (by decide)
       simp [htgt, htgtAfter, e1, e2, e3]; try omega))

/-- If `tryFixupSlot c s = some m`, then applying `m` to `c` gives a cube with
exactly one more white U-target. -/
theorem tryFixupSlot_progress (c : PRubik) (s : Slot) (m : Moves)
    (hm : tryFixupSlot c s = some m) :
    numWhiteUTargets (c * PRubik.move m) = numWhiteUTargets c + 1 := by
  unfold tryFixupSlot at hm
  -- Walk through the nested ifs.
  by_cases htgt : whiteAt c s.target
  · simp [htgt] at hm
  by_cases h2 : whiteAt c (caseSource s .F2)
  · simp [htgt, h2] at hm; subst hm; exact caseMoves_count_progress c s .F2 htgt h2
  by_cases h6 : whiteAt c (caseSource s .F6)
  · simp [htgt, h2, h6] at hm; subst hm; exact caseMoves_count_progress c s .F6 htgt h6
  by_cases h4 : whiteAt c (caseSource s .R4)
  · simp [htgt, h2, h6, h4] at hm; subst hm; exact caseMoves_count_progress c s .R4 htgt h4
  by_cases h8 : whiteAt c (caseSource s .F8)
  · simp [htgt, h2, h6, h4, h8] at hm; subst hm; exact caseMoves_count_progress c s .F8 htgt h8
  by_cases hd : whiteAt c (caseSource s .D2)
  · simp [htgt, h2, h6, h4, h8, hd] at hm; subst hm; exact caseMoves_count_progress c s .D2 htgt hd
  · simp [htgt, h2, h6, h4, h8, hd] at hm

/-- Helper: if `tryAnyFixupOpt c = some m`, then count increases by 1. -/
theorem tryAnyFixupOpt_progress (c : PRubik) (m : Moves)
    (hm : tryAnyFixupOpt c = some m) :
    numWhiteUTargets (c * PRubik.move m) = numWhiteUTargets c + 1 := by
  unfold tryAnyFixupOpt at hm
  match h1 : tryFixupSlot c Slot.UF with
  | some m1 =>
    rw [h1] at hm
    have heq : m1 = m := Option.some.inj hm
    rw [← heq]
    exact tryFixupSlot_progress c Slot.UF m1 h1
  | none =>
    rw [h1] at hm
    match h2 : tryFixupSlot c Slot.UR with
    | some m2 =>
      rw [h2] at hm
      have heq : m2 = m := Option.some.inj hm
      rw [← heq]
      exact tryFixupSlot_progress c Slot.UR m2 h2
    | none =>
      rw [h2] at hm
      match h3 : tryFixupSlot c Slot.UB with
      | some m3 =>
        rw [h3] at hm
        have heq : m3 = m := Option.some.inj hm
        rw [← heq]
        exact tryFixupSlot_progress c Slot.UB m3 h3
      | none =>
        rw [h3] at hm
        exact tryFixupSlot_progress c Slot.UL m hm

/-- If the U-rotated fixup returns `some m`, the count increases by 1. -/
theorem tryFixupWithUk_progress (c : PRubik) (k : Nat) (m : Moves)
    (hm : tryFixupWithUk c k = some m) :
    numWhiteUTargets (c * PRubik.move m) = numWhiteUTargets c + 1 := by
  unfold tryFixupWithUk at hm
  simp only at hm
  cases hopt : tryAnyFixupOpt (c * PRubik.move (List.replicate k Orientation.U))
    with
  | none => rw [hopt] at hm; simp at hm
  | some m' =>
    rw [hopt] at hm
    simp at hm
    subst hm
    rw [PRubik.move_append, ← mul_assoc,
      tryAnyFixupOpt_progress _ m' hopt, numWhiteUTargets_Uk]

/-- The combined fixup either preserves the cube or increases the count. -/
theorem tryAnyFixup_progress (c : PRubik) :
    tryAnyFixup c = [] ∨
    numWhiteUTargets (c * PRubik.move (tryAnyFixup c)) = numWhiteUTargets c + 1 := by
  unfold tryAnyFixup
  -- Case-split on each tryFixupWithUk
  by_cases h0 : (tryFixupWithUk c 0).isSome
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h0
    right
    rw [hm, Option.getD_some]
    exact tryFixupWithUk_progress c 0 m hm
  · simp [Option.not_isSome_iff_eq_none] at h0
    rw [h0]
    by_cases h1 : (tryFixupWithUk c 1).isSome
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h1
      right
      rw [hm, Option.getD_some]
      exact tryFixupWithUk_progress c 1 m hm
    · simp [Option.not_isSome_iff_eq_none] at h1
      rw [h1]
      by_cases h2 : (tryFixupWithUk c 2).isSome
      · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h2
        right
        rw [hm, Option.getD_some]
        exact tryFixupWithUk_progress c 2 m hm
      · simp [Option.not_isSome_iff_eq_none] at h2
        rw [h2]
        by_cases h3 : (tryFixupWithUk c 3).isSome
        · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h3
          right
          rw [hm, Option.getD_some]
          exact tryFixupWithUk_progress c 3 m hm
        · simp [Option.not_isSome_iff_eq_none] at h3
          rw [h3]
          left; rfl

/-! ## Existence of a fire when daisy not done

If `¬ daisyDone c`, the algorithm fires.

Argument structure:
* **Pair structure.** For each `s`, `caseSource s F2 = s.target.flip`. By
  `PRubik.edge_flip`, the labels at paired positions are flips, so at most one
  of the two stickers in any U-pair shows white.
* **Subclaim 1.** If any middle/D position is white in `c`, the failure
  assumption forces all 4 U-targets to be white (via `whiteAt_Uk_target`
  cycle), contradicting `¬ daisyDone`.
* **Pigeonhole.** Each white edge piece labelled `s.target` lives at the
  position `whitePos c s := edgePieceEquiv.symm s.target`. The 4 such
  positions are distinct, all in the U-layer (Subclaim 1), and pairwise
  pair-distinct. So they distribute one per U-pair.
* **Conclusion.** The U-pair of the failed slot `sFail` contains some
  `whitePos c s_pre`, which is white. Since `sFail.target` is not white, this
  white is at `caseSource sFail F2`, contradicting failure. -/

/-! ### Pair structure -/

theorem caseSource_F2_eq_target_flip (s : Slot) :
    caseSource s .F2 = s.target.flip := by cases s <;> rfl

theorem not_whiteAt_pair (c : PRubik) (e : EdgePiece) :
    ¬ (whiteAt c e ∧ whiteAt c e.flip) := by
  rintro ⟨h1, h2⟩
  unfold whiteAt at h1 h2
  rw [c.edge_flip, EdgePiece.flip_fst] at h2
  exact (c.edgePieceEquiv e).isAdjacent.ne (h1.trans h2.symm)

/-! ### Slot.uNext is a 4-cycle -/

theorem Slot.uNext_iter_surj (target s : Slot) :
    ∃ k : Nat, k < 4 ∧ Slot.uNext^[k] s = target := by
  cases target <;> cases s <;>
    first
      | exact ⟨0, by decide, rfl⟩
      | exact ⟨1, by decide, rfl⟩
      | exact ⟨2, by decide, rfl⟩
      | exact ⟨3, by decide, rfl⟩

/-! ### U fixes middle/D source positions; cycles target positions -/

theorem ofOrientation_U_caseSource_F6 (s : Slot) :
    (PRubik.ofOrientation Orientation.U).edgePieceEquiv (caseSource s .F6) =
      caseSource s .F6 := by
  cases s <;> decide

theorem ofOrientation_U_caseSource_R4 (s : Slot) :
    (PRubik.ofOrientation Orientation.U).edgePieceEquiv (caseSource s .R4) =
      caseSource s .R4 := by
  cases s <;> decide

theorem ofOrientation_U_caseSource_F8 (s : Slot) :
    (PRubik.ofOrientation Orientation.U).edgePieceEquiv (caseSource s .F8) =
      caseSource s .F8 := by
  cases s <;> decide

theorem ofOrientation_U_caseSource_D2 (s : Slot) :
    (PRubik.ofOrientation Orientation.U).edgePieceEquiv (caseSource s .D2) =
      caseSource s .D2 := by
  cases s <;> decide

theorem move_Uk_caseSource_middleD (k : Nat) (s : Slot) (t : CaseTag)
    (h : t ≠ .F2) :
    (PRubik.move (List.replicate k Orientation.U)).edgePieceEquiv (caseSource s t) =
      caseSource s t := by
  induction k with
  | zero => simp
  | succ n IH =>
    rw [List.replicate_succ, ← List.singleton_append, PRubik.move_append,
        edgePieceEquiv_mul, Equiv.Perm.mul_apply, IH, move_singleton]
    cases t
    · exact absurd rfl h
    · exact ofOrientation_U_caseSource_F6 s
    · exact ofOrientation_U_caseSource_R4 s
    · exact ofOrientation_U_caseSource_F8 s
    · exact ofOrientation_U_caseSource_D2 s

theorem whiteAt_Uk_middleD (c : PRubik) (k : Nat) (s : Slot) (t : CaseTag)
    (h : t ≠ .F2) :
    whiteAt (c * PRubik.move (List.replicate k Orientation.U)) (caseSource s t) ↔
    whiteAt c (caseSource s t) := by
  unfold whiteAt
  rw [edgePieceEquiv_mul, Equiv.Perm.mul_apply,
      move_Uk_caseSource_middleD k s t h]

theorem whiteAt_Uk_target (c : PRubik) (k : Nat) (s : Slot) :
    whiteAt (c * PRubik.move (List.replicate k Orientation.U)) s.target ↔
    whiteAt c (Slot.uNext^[k] s).target := by
  induction k generalizing c s with
  | zero => simp
  | succ n IH =>
    have hiter : Slot.uNext^[n + 1] s = Slot.uNext (Slot.uNext^[n] s) :=
      Function.iterate_succ_apply' Slot.uNext n s
    rw [List.replicate_succ, ← List.singleton_append, PRubik.move_append,
        ← mul_assoc, move_singleton, IH, whiteAt_U_cycle, hiter]

/-! ### Algorithm-failure helpers -/

theorem tryFixupSlot_none_of_tryAnyFixupOpt_none (c : PRubik) (s : Slot)
    (h : tryAnyFixupOpt c = none) : tryFixupSlot c s = none := by
  unfold tryAnyFixupOpt at h
  match hUF : tryFixupSlot c .UF with
  | some _ => rw [hUF] at h; exact Option.noConfusion h
  | none =>
    rw [hUF] at h
    match hUR : tryFixupSlot c .UR with
    | some _ => rw [hUR] at h; exact Option.noConfusion h
    | none =>
      rw [hUR] at h
      match hUB : tryFixupSlot c .UB with
      | some _ => rw [hUB] at h; exact Option.noConfusion h
      | none =>
        rw [hUB] at h
        cases s
        · exact hUF
        · exact hUR
        · exact hUB
        · exact h

theorem tryAnyFixupOpt_none_of_tryFixupWithUk_none (c : PRubik) (k : Nat)
    (h : tryFixupWithUk c k = none) :
    tryAnyFixupOpt (c * PRubik.move (List.replicate k Orientation.U)) = none := by
  unfold tryFixupWithUk at h
  simp only at h
  match h' : tryAnyFixupOpt (c * PRubik.move (List.replicate k Orientation.U)) with
  | none => rfl
  | some _ => rw [h'] at h; simp at h

theorem tryFixupSlot_target_white_of_source_white (c : PRubik) (s : Slot)
    (t : CaseTag) (h_none : tryFixupSlot c s = none)
    (h_source : whiteAt c (caseSource s t)) : whiteAt c s.target := by
  by_contra htgt
  unfold tryFixupSlot at h_none
  rw [if_neg htgt] at h_none
  cases t
  · rw [if_pos h_source] at h_none; exact Option.noConfusion h_none
  · by_cases h2 : whiteAt c (caseSource s .F2)
    · rw [if_pos h2] at h_none; exact Option.noConfusion h_none
    · rw [if_neg h2, if_pos h_source] at h_none; exact Option.noConfusion h_none
  · by_cases h2 : whiteAt c (caseSource s .F2)
    · rw [if_pos h2] at h_none; exact Option.noConfusion h_none
    rw [if_neg h2] at h_none
    by_cases h6 : whiteAt c (caseSource s .F6)
    · rw [if_pos h6] at h_none; exact Option.noConfusion h_none
    · rw [if_neg h6, if_pos h_source] at h_none; exact Option.noConfusion h_none
  · by_cases h2 : whiteAt c (caseSource s .F2)
    · rw [if_pos h2] at h_none; exact Option.noConfusion h_none
    rw [if_neg h2] at h_none
    by_cases h6 : whiteAt c (caseSource s .F6)
    · rw [if_pos h6] at h_none; exact Option.noConfusion h_none
    rw [if_neg h6] at h_none
    by_cases h4 : whiteAt c (caseSource s .R4)
    · rw [if_pos h4] at h_none; exact Option.noConfusion h_none
    · rw [if_neg h4, if_pos h_source] at h_none; exact Option.noConfusion h_none
  · by_cases h2 : whiteAt c (caseSource s .F2)
    · rw [if_pos h2] at h_none; exact Option.noConfusion h_none
    rw [if_neg h2] at h_none
    by_cases h6 : whiteAt c (caseSource s .F6)
    · rw [if_pos h6] at h_none; exact Option.noConfusion h_none
    rw [if_neg h6] at h_none
    by_cases h4 : whiteAt c (caseSource s .R4)
    · rw [if_pos h4] at h_none; exact Option.noConfusion h_none
    rw [if_neg h4] at h_none
    by_cases h8 : whiteAt c (caseSource s .F8)
    · rw [if_pos h8] at h_none; exact Option.noConfusion h_none
    · rw [if_neg h8, if_pos h_source] at h_none; exact Option.noConfusion h_none

/-! ### Subclaim 1: middle/D white forces daisyDone -/

theorem subclaim1 (c : PRubik) (s : Slot) (t : CaseTag) (ht : t ≠ .F2)
    (h_white : whiteAt c (caseSource s t))
    (h_fail : ∀ k : Nat, k < 4 → tryFixupWithUk c k = none) :
    daisyDone c := by
  have key : ∀ k : Nat, k < 4 → whiteAt c (Slot.uNext^[k] s).target := by
    intro k hk
    have h_src_k :
        whiteAt (c * PRubik.move (List.replicate k Orientation.U))
          (caseSource s t) := by
      rw [whiteAt_Uk_middleD c k s t ht]; exact h_white
    have h_opt :
        tryAnyFixupOpt (c * PRubik.move (List.replicate k Orientation.U)) = none :=
      tryAnyFixupOpt_none_of_tryFixupWithUk_none c k (h_fail k hk)
    have h_slot_none :
        tryFixupSlot (c * PRubik.move (List.replicate k Orientation.U)) s = none :=
      tryFixupSlot_none_of_tryAnyFixupOpt_none _ _ h_opt
    have h_tgt_k :
        whiteAt (c * PRubik.move (List.replicate k Orientation.U)) s.target :=
      tryFixupSlot_target_white_of_source_white _ _ _ h_slot_none h_src_k
    rwa [whiteAt_Uk_target] at h_tgt_k
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (
    obtain ⟨k, hk, hk_eq⟩ := Slot.uNext_iter_surj _ s
    have := key k hk
    rwa [hk_eq] at this)

/-! ### Pigeonhole on the 4 white-piece positions -/

/-- The position in `c` of the white piece originally labelled `s.target`. -/
def Slot.whitePos (c : PRubik) (s : Slot) : EdgePiece :=
  c.edgePieceEquiv.symm s.target

theorem whiteAt_whitePos (c : PRubik) (s : Slot) : whiteAt c (s.whitePos c) := by
  unfold whiteAt Slot.whitePos
  rw [Equiv.apply_symm_apply]
  cases s <;> rfl

theorem whitePos_injective (c : PRubik) :
    Function.Injective (fun s : Slot => s.whitePos c) := by
  intro s s' h
  unfold Slot.whitePos at h
  have heq : s.target = s'.target := c.edgePieceEquiv.symm.injective h
  cases s <;> cases s' <;>
    first | rfl | (revert heq; decide)

theorem whitePos_pair_distinct (c : PRubik) (s s' : Slot) (h : s ≠ s') :
    s.whitePos c ≠ (s'.whitePos c).flip := by
  intro heq
  unfold Slot.whitePos at heq
  apply_fun c.edgePieceEquiv at heq
  rw [Equiv.apply_symm_apply, c.edge_flip, Equiv.apply_symm_apply] at heq
  apply h
  cases s <;> cases s' <;>
    first | rfl | (revert heq; decide)

/-- Under failure + ¬daisyDone, `whitePos s` is in the U-layer (not at any
non-F2 caseSource position). -/
theorem whitePos_not_middleD (c : PRubik)
    (h_fail : ∀ k : Nat, k < 4 → tryFixupWithUk c k = none)
    (h_not_done : ¬ daisyDone c) (s : Slot) (s' : Slot) (t' : CaseTag)
    (ht' : t' ≠ .F2) : s.whitePos c ≠ caseSource s' t' := by
  intro heq
  apply h_not_done
  have h_white : whiteAt c (caseSource s' t') := heq ▸ whiteAt_whitePos c s
  exact subclaim1 c s' t' ht' h_white h_fail

/-- The U-pair slot containing `q`, if `q` is in the U-layer. -/
def upairOf? (q : EdgePiece) : Option Slot :=
  if q = Slot.UF.target ∨ q = caseSource .UF .F2 then some .UF
  else if q = Slot.UR.target ∨ q = caseSource .UR .F2 then some .UR
  else if q = Slot.UB.target ∨ q = caseSource .UB .F2 then some .UB
  else if q = Slot.UL.target ∨ q = caseSource .UL .F2 then some .UL
  else none

/-- For any U-layer position (= not at a middle/D caseSource), `upairOf?`
returns `some`. -/
theorem upairOf?_isSome_of_not_middleD (q : EdgePiece)
    (h : ∀ s' : Slot, ∀ t' : CaseTag, t' ≠ .F2 → q ≠ caseSource s' t') :
    (upairOf? q).isSome := by
  unfold upairOf?
  by_cases h1 : q = Slot.UF.target ∨ q = caseSource .UF .F2
  · simp [h1]
  by_cases h2 : q = Slot.UR.target ∨ q = caseSource .UR .F2
  · simp [h1, h2]
  by_cases h3 : q = Slot.UB.target ∨ q = caseSource .UB .F2
  · simp [h1, h2, h3]
  by_cases h4 : q = Slot.UL.target ∨ q = caseSource .UL .F2
  · simp [h1, h2, h3, h4]
  · exfalso
    push_neg at h1 h2 h3 h4
    -- q must be a middle/D position. Enumerate via decide.
    have hcontra : ∀ q' : EdgePiece,
        q' ≠ Slot.UF.target → q' ≠ caseSource .UF .F2 →
        q' ≠ Slot.UR.target → q' ≠ caseSource .UR .F2 →
        q' ≠ Slot.UB.target → q' ≠ caseSource .UB .F2 →
        q' ≠ Slot.UL.target → q' ≠ caseSource .UL .F2 →
        (q' = caseSource .UF .F6 ∨ q' = caseSource .UF .R4 ∨
          q' = caseSource .UF .F8 ∨ q' = caseSource .UF .D2 ∨
          q' = caseSource .UR .F6 ∨ q' = caseSource .UR .R4 ∨
          q' = caseSource .UR .F8 ∨ q' = caseSource .UR .D2 ∨
          q' = caseSource .UB .F6 ∨ q' = caseSource .UB .R4 ∨
          q' = caseSource .UB .F8 ∨ q' = caseSource .UB .D2 ∨
          q' = caseSource .UL .F6 ∨ q' = caseSource .UL .R4 ∨
          q' = caseSource .UL .F8 ∨ q' = caseSource .UL .D2) := by decide
    have := hcontra q h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h .UF .F6 (by decide) rfl
    · exact h .UF .R4 (by decide) rfl
    · exact h .UF .F8 (by decide) rfl
    · exact h .UF .D2 (by decide) rfl
    · exact h .UR .F6 (by decide) rfl
    · exact h .UR .R4 (by decide) rfl
    · exact h .UR .F8 (by decide) rfl
    · exact h .UR .D2 (by decide) rfl
    · exact h .UB .F6 (by decide) rfl
    · exact h .UB .R4 (by decide) rfl
    · exact h .UB .F8 (by decide) rfl
    · exact h .UB .D2 (by decide) rfl
    · exact h .UL .F6 (by decide) rfl
    · exact h .UL .R4 (by decide) rfl
    · exact h .UL .F8 (by decide) rfl
    · exact h .UL .D2 (by decide) rfl

theorem upairOf?_eq_some_iff (q : EdgePiece) (s : Slot) :
    upairOf? q = some s ↔ q = s.target ∨ q = caseSource s .F2 := by
  cases s <;> revert q <;> decide

/-- The pair-slot map (with junk for non-U-layer). Use only when input is in U-layer. -/
def pairSlotOf (c : PRubik) (s : Slot) : Slot :=
  (upairOf? (s.whitePos c)).getD .UF

theorem pairSlotOf_correct (c : PRubik)
    (h_fail : ∀ k : Nat, k < 4 → tryFixupWithUk c k = none)
    (h_not_done : ¬ daisyDone c) (s : Slot) :
    s.whitePos c = (pairSlotOf c s).target ∨
    s.whitePos c = caseSource (pairSlotOf c s) .F2 := by
  unfold pairSlotOf
  have hsome : (upairOf? (s.whitePos c)).isSome :=
    upairOf?_isSome_of_not_middleD _ (whitePos_not_middleD c h_fail h_not_done s)
  obtain ⟨s', heq⟩ := Option.isSome_iff_exists.mp hsome
  rw [heq, Option.getD_some]
  exact (upairOf?_eq_some_iff _ _).mp heq

theorem pairSlotOf_injective (c : PRubik)
    (h_fail : ∀ k : Nat, k < 4 → tryFixupWithUk c k = none)
    (h_not_done : ¬ daisyDone c) :
    Function.Injective (pairSlotOf c) := by
  intro s s' heq
  -- whitePos c s, whitePos c s' both in U-pair (pairSlotOf c s = pairSlotOf c s').
  -- So they're either equal or pair-partners.
  -- Equal ⇒ s = s' (whitePos_injective).
  -- Pair-partners ⇒ contradicts pair-distinctness if s ≠ s'.
  by_contra hne
  have hpair : s.whitePos c = (pairSlotOf c s).target ∨
               s.whitePos c = caseSource (pairSlotOf c s) .F2 :=
    pairSlotOf_correct c h_fail h_not_done s
  have hpair' : s'.whitePos c = (pairSlotOf c s').target ∨
                s'.whitePos c = caseSource (pairSlotOf c s') .F2 :=
    pairSlotOf_correct c h_fail h_not_done s'
  rw [← heq] at hpair'
  -- Now both are in {pairSlotOf c s . target, caseSource (pairSlotOf c s) F2}
  -- Either both equal, or they are pair-partners.
  have hpos_neq : s.whitePos c ≠ s'.whitePos c := fun he =>
    hne (whitePos_injective c he)
  have hflip : caseSource (pairSlotOf c s) .F2 = (pairSlotOf c s).target.flip :=
    caseSource_F2_eq_target_flip _
  rcases hpair with h1 | h1 <;> rcases hpair' with h2 | h2
  · exact hpos_neq (h1.trans h2.symm)
  · -- s.whitePos = target, s'.whitePos = F2-source = target.flip
    rw [hflip] at h2
    -- h2 : s'.whitePos = (pairSlotOf c s).target.flip = s.whitePos.flip (using h1)
    rw [← h1] at h2
    exact whitePos_pair_distinct c s' s (Ne.symm hne) h2
  · rw [hflip] at h1
    rw [← h2] at h1
    exact whitePos_pair_distinct c s s' hne h1
  · exact hpos_neq (h1.trans h2.symm)

theorem pairSlotOf_surjective (c : PRubik)
    (h_fail : ∀ k : Nat, k < 4 → tryFixupWithUk c k = none)
    (h_not_done : ¬ daisyDone c) :
    Function.Surjective (pairSlotOf c) :=
  Finite.injective_iff_surjective.mp (pairSlotOf_injective c h_fail h_not_done)

/-! ### Final lemma -/

theorem tryAnyFixup_nonempty_of_not_done (c : PRubik) (h : ¬ daisyDone c) :
    tryAnyFixup c ≠ [] := by
  intro hempty
  -- Step 1: Extract failure of all tryFixupWithUk c k for k < 4.
  have h_fail : ∀ k : Nat, k < 4 → tryFixupWithUk c k = none := by
    intro k hk
    unfold tryAnyFixup at hempty
    -- Cases on each tryFixupWithUk c i for i = 0, 1, 2, 3.
    have aux : ∀ i : Nat, ∀ m : Moves, tryFixupWithUk c i = some m → m ≠ [] := by
      intro i m hm hm_nil
      have := tryFixupWithUk_progress c i m hm
      rw [hm_nil, PRubik.move_nil, mul_one] at this
      omega
    match h0 : tryFixupWithUk c 0 with
    | some m0 =>
      rw [h0] at hempty; simp at hempty
      exact absurd hempty (aux 0 m0 h0)
    | none =>
      rw [h0] at hempty; simp at hempty
      match h1 : tryFixupWithUk c 1 with
      | some m1 =>
        rw [h1] at hempty; simp at hempty
        exact absurd hempty (aux 1 m1 h1)
      | none =>
        rw [h1] at hempty; simp at hempty
        match h2 : tryFixupWithUk c 2 with
        | some m2 =>
          rw [h2] at hempty; simp at hempty
          exact absurd hempty (aux 2 m2 h2)
        | none =>
          rw [h2] at hempty; simp at hempty
          match h3 : tryFixupWithUk c 3 with
          | some m3 =>
            rw [h3] at hempty; simp at hempty
            exact absurd hempty (aux 3 m3 h3)
          | none =>
            interval_cases k
            · exact h0
            · exact h1
            · exact h2
            · exact h3
  -- Step 2: Find a failed slot sFail.
  have hex_fail : ∃ sFail : Slot, ¬ whiteAt c sFail.target := by
    by_contra hno
    push_neg at hno
    exact h ⟨hno .UF, hno .UR, hno .UB, hno .UL⟩
  obtain ⟨sFail, hfail⟩ := hex_fail
  -- Step 3: Find s_pre with pairSlotOf c s_pre = sFail (surjectivity).
  obtain ⟨s_pre, hpre⟩ := pairSlotOf_surjective c h_fail h sFail
  -- Step 4: whitePos c s_pre is at U-pair of sFail. Since target sFail not white,
  -- whitePos c s_pre = caseSource sFail F2.
  have hpos : s_pre.whitePos c = sFail.target ∨ s_pre.whitePos c = caseSource sFail .F2 := by
    have := pairSlotOf_correct c h_fail h s_pre
    rw [hpre] at this
    exact this
  have hwhite_pre : whiteAt c (s_pre.whitePos c) := whiteAt_whitePos c s_pre
  have hwhite_F2 : whiteAt c (caseSource sFail .F2) := by
    rcases hpos with h1 | h1
    · rw [h1] at hwhite_pre; exact absurd hwhite_pre hfail
    · rw [h1] at hwhite_pre; exact hwhite_pre
  -- Step 5: tryFixupSlot c sFail matches F2 case, so returns some (caseMoves sFail F2).
  have hslot : tryFixupSlot c sFail = some (caseMoves sFail .F2) := by
    unfold tryFixupSlot
    rw [if_neg hfail, if_pos hwhite_F2]
  -- Step 6: tryAnyFixupOpt c ≠ none (since some slot returns some).
  have hopt_ne : tryAnyFixupOpt c ≠ none := by
    intro hopt
    have := tryFixupSlot_none_of_tryAnyFixupOpt_none c sFail hopt
    rw [this] at hslot
    exact Option.noConfusion hslot
  -- Step 7: tryFixupWithUk c 0 ≠ none, contradicting h_fail 0.
  have hwithUk0_ne : tryFixupWithUk c 0 ≠ none := fun h0 =>
    hopt_ne (tryAnyFixupOpt_none_of_tryFixupWithUk_none c 0 h0)
  exact hwithUk0_ne (h_fail 0 (by decide))

/-! ## Main correctness theorem -/

/-- numWhiteUTargets is bounded by 4. -/
theorem numWhiteUTargets_le_four (c : PRubik) : numWhiteUTargets c ≤ 4 := by
  unfold numWhiteUTargets
  by_cases h1 : whiteAt c Slot.UF.target <;>
  by_cases h2 : whiteAt c Slot.UR.target <;>
  by_cases h3 : whiteAt c Slot.UB.target <;>
  by_cases h4 : whiteAt c Slot.UL.target <;>
  simp [h1, h2, h3, h4]

/-- One step of the algorithm achieves at least the count's minimum increase. -/
theorem progress_one_step (c : PRubik) :
    numWhiteUTargets (c * PRubik.move (tryAnyFixup c)) ≥
      min (numWhiteUTargets c + 1) 4 := by
  rcases tryAnyFixup_progress c with h | h
  · rw [h, PRubik.move_nil, mul_one]
    -- Goal: numWhiteUTargets c ≥ min(numWhiteUTargets c + 1, 4)
    -- Need: numWhiteUTargets c ≥ 4 (i.e. daisy done) when tryAnyFixup = []
    by_contra hcontra
    push_neg at hcontra
    have hlt : numWhiteUTargets c < 4 := by
      have := numWhiteUTargets_le_four c
      omega
    have hne : ¬ daisyDone c := fun hdone => by
      rw [daisyDone_iff_count] at hdone
      omega
    exact tryAnyFixup_nonempty_of_not_done c hne h
  · rw [h]; omega

/-- Iterate the bound: 4 applications of `tryAnyFixup` reach count 4. -/
theorem progress_four_steps (c : PRubik) :
    numWhiteUTargets (c * PRubik.move (tryAnyFixup c)
      * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)))
      * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)
          * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)))))
      * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)
          * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)))
          * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)
              * PRubik.move (tryAnyFixup (c * PRubik.move (tryAnyFixup c)))))))) = 4 := by
  set c1 := c * PRubik.move (tryAnyFixup c) with hc1
  set c2 := c1 * PRubik.move (tryAnyFixup c1) with hc2
  set c3 := c2 * PRubik.move (tryAnyFixup c2) with hc3
  set c4 := c3 * PRubik.move (tryAnyFixup c3) with hc4
  have h1 := progress_one_step c
  have h2 := progress_one_step c1
  have h3 := progress_one_step c2
  have h4 := progress_one_step c3
  have b := numWhiteUTargets_le_four c4
  rw [← hc1] at h1
  rw [← hc2] at h2
  rw [← hc3] at h3
  rw [← hc4] at h4
  omega

theorem daisyMoves_correct (c : PRubik) :
    daisyDone (c * PRubik.move (daisyMoves c)) := by
  rw [daisyDone_iff_count]
  unfold daisyMoves
  -- The result is c * move (m1 ++ m2 ++ m3 ++ m4)
  -- Distribute moves and rewrite to chain of multiplications
  simp only [PRubik.move_append, ← mul_assoc]
  exact progress_four_steps c

end Daisy
