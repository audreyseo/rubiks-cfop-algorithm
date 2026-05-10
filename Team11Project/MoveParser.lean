import Rubik
import Rubik.PRubik
import Rubik.Orientation
/-



-/

#check Rubik.move

#check Orientation.R

#check Stickers.Solved

#eval Stickers.toPRubik Stickers.Solved

#check Moves.B

#eval (Stickers.toPRubik Stickers.Solved) * PRubik.move Moves.B

def solved := Stickers.toPRubik Stickers.Solved

instance : Coe (List Moves) Moves where
  coe ms := ms.flatten


def charToMove : Char → (Except String Moves)
  | 'F' => Except.ok Moves.F
  | 'B' => .ok Moves.B
  | 'U' => .ok Moves.F
  | 'D' => .ok Moves.D
  | 'R' => .ok Moves.R
  | 'L' => .ok Moves.L
  | c => .error s!"Improper char in Rubik's cube move: {c}"

def parseMoves (s: String) : Except String Moves :=
  let rec parserHelper : List Char → Except String Moves → Except String Moves
    | [], acc => acc
    | ' ' :: ms, acc =>
      parserHelper ms acc
    | c :: '\'' :: ms, acc' => do
      let char ← charToMove c
      let acc ← acc'
      parserHelper ms (pure (acc ++ char ++ char ++ char))
    | c :: '2' :: ms, acc' => do
      let char ← charToMove c
      let acc ← acc'
      parserHelper ms (pure (acc ++ char ++ char))
    | c :: ms, acc' => do
      let char ← charToMove c
      let acc ← acc'
      parserHelper ms (pure (acc ++ char))
      /- Except.error s!"Could not parse Rubik's cube move string {s}" -/
  try
    parserHelper s.toList (Except.ok [])
  catch e =>
    .error s!"Could not parse Rubik's cube move string \"{s}\""
      

#eval solved * PRubik.move (Moves.R ++ Moves.F ++ Moves.B ++ Moves.F ++ Moves.R)

-- vanilla move string, should be fine
#eval parseMoves "F R U' D2 R'"
-- fails currently, M is an actual move but it is not supported currently
-- M is equivalent to L R' x
#eval parseMoves "F B L M"
-- should also fail, though r is kind of like L x
#eval parseMoves "R r x' L'" -- r x' L' is the identity

