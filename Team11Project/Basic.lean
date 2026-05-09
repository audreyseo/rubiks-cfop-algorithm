import Rubik

-- ```
--          00 01 02
--          03  U 04
--          05 06 07
-- 08 09 10 16 17 18 24 25 26
-- 11  L 12 19  F 20 27  R 28
-- 13 14 15 21 22 23 29 30 31
--          32 33 34
--          35  D 36
--          37 38 39
--          40 41 42
--          43  B 44
--          45 46 47
-- ```

-- R' U' R U R' swaps 17 <-> 25 and 06 <-> 04, while leaving fixed 01, 03, 09, 46.

open Orientation in
example :
    let m : Moves := Moves.R' ++ Moves.U' ++ Moves.R ++ Moves.U ++ Moves.R'
    let p := (PRubik.move m).edgePieceEquiv
    p (EdgePiece.mk' F U) = EdgePiece.mk' R U ∧
    p (EdgePiece.mk' R U) = EdgePiece.mk' F U ∧
    p (EdgePiece.mk' U F) = EdgePiece.mk' U R ∧
    p (EdgePiece.mk' U R) = EdgePiece.mk' U F ∧
    p (EdgePiece.mk' U B) = EdgePiece.mk' U B ∧
    p (EdgePiece.mk' U L) = EdgePiece.mk' U L ∧
    p (EdgePiece.mk' L U) = EdgePiece.mk' L U ∧
    p (EdgePiece.mk' B U) = EdgePiece.mk' B U := by
  decide
