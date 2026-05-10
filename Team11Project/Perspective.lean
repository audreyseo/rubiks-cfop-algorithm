import Rubik
import Rubik.Orientation
import Team11Project.MoveParser

#print Moves

structure Perspective where
  perspective : Orientation → Orientation := (fun x => x)


inductive Faces where
  | F
  | B
  | R
  | L
  | U
  | D : Faces

structure FacesPerspective where
  perspective : Faces → Faces := (fun x => x)


inductive Axes where
  | x
  | y
  | z : Axes

@[reducible]
def orientationToFaces : Orientation → Faces
  | (true, Axis.x) => .R
  | (true, Axis.y) => .U
  | (true, Axis.z) => .F
  | (false, Axis.x) => .L
  | (false, Axis.y) => .D
  | (false, Axis.z) => .B

@[reducible]
def facesToOrientation : Faces → Orientation
  | .R => (true, Axis.x)
  | .U => (true, .y)
  | .F => (true, .z)
  | .L => (false, .x)
  | .D => (false, .y)
  | .B => (false, .z)




@[reducible]
def Perspective.x (o: Orientation) : Orientation :=
  facesToOrientation (match orientationToFaces o with
                      | .R => .R
                      | .U => .F
                      | .F => .D
                      | .L => .L
                      | .D => .B
                      | .B => .U)

@[reducible]
def FacesPerspective.x : Faces → Faces
  | .R => .R
  | .U => .F
  | .F => .D
  | .L => .L
  | .D => .B
  | .B => .U

@[reducible]
def Perspective.y (o : Orientation) : Orientation :=
  facesToOrientation (match orientationToFaces o with
                      | .R => .U
                      | .U => .L
                      | .F => .F
                      | .L => .D
                      | .D => .R
                      | .B => .B)

def FacesPerspective.y : Faces → Faces
  | .R => .U
  | .U => .L
  | .F => .F
  | .L => .D
  | .D => .R
  | .B => .B

@[reducible]
def Perspective.z (o : Orientation) : Orientation :=
  facesToOrientation (match orientationToFaces o with
                      | .R => .B
                      | .U => .U
                      | .F => .R
                      | .L => .F
                      | .D => .D
                      | .B => .L)

@[reducible]
def FacesPerspective.z : Faces → Faces
  | .R => .B
  | .U => .U
  | .F => .R
  | .L => .F
  | .D => .D
  | .B => .L

#eval Moves.B.map Perspective.z
#eval Moves.U.map Perspective.x
#eval Moves.F.map (Perspective.x ∘ Perspective.y)

inductive ExtendedMoves where
  | R
  | U
  | F
  | L
  | D
  | B
  | x
  | y
  | z
deriving Repr

instance : ToString ExtendedMoves where
  toString
    | .R => "R"
    | .U => "U"
    | .F => "F"
    | .L => "L"
    | .D => "D"
    | .B => "B"
    | .x => "x"
    | .y => "y"
    | .z => "z"

def ExtendedMoves.ofFaces : Faces → ExtendedMoves
  | .R => .R
  | .U => .U
  | .F => .F
  | .L => .L
  | .D => .D
  | .B => .B

instance : ToString Faces where
  toString f := toString (ExtendedMoves.ofFaces f)

def ExtendedMoves.isFace : ExtendedMoves → Bool
  | .R | .U | .F | .L | .D | .B =>
    true
  | _ =>
    false

def ExtendedMoves.toFace : ExtendedMoves → Except String Faces
  | .R => pure .R
  | .U => pure .U
  | .F => pure .F
  | .L => pure .L
  | .D => pure .D
  | .B => pure .B
  | em => .error s!"Not one of the basic faces (R, U, F, L, D, B): {em}"

/- abbrev MoveParser (α : Type) : Type := ReaderT Perspective (Except String) α  -/
def MoveParser (α : Type) : Type :=
  FacesPerspective → Except String α

instance : Monad MoveParser where
  pure x := fun _ => pure x
  bind result next :=
    fun cfg => do
      let v ← result cfg
      next v cfg

def MoveParser.run (action: MoveParser α) (p: FacesPerspective) : Except String α :=
  action p

def currentPerspective : MoveParser FacesPerspective :=
  fun p => pure p

def locally (change: FacesPerspective → FacesPerspective) (action: MoveParser α) : MoveParser α :=
  fun p => action (change p)

def doExcept (action: Except String Faces) : MoveParser Faces :=
  fun p => p.perspective <$> action

def doExceptGeneral (action: Except String α) : MoveParser α :=
  fun _ => action

def addMove (m: Moves) : MoveParser Moves :=
  doExceptGeneral (Except.ok m)


def Perspective.changePerspective (e: ExtendedMoves) (p: Perspective) : Perspective :=
  match e with
  | .x => { perspective := Perspective.x ∘ p.perspective }
  | .y => { perspective := Perspective.y ∘ p.perspective }
  | .z => { perspective := Perspective.z ∘ p.perspective }
  | _ => p

def FacesPerspective.changePerspective (e: ExtendedMoves) (p: FacesPerspective) : FacesPerspective :=
  match e with
  | .x => { perspective := FacesPerspective.x ∘ p.perspective }
  | .y => { perspective := FacesPerspective.y ∘ p.perspective }
  | .z => { perspective := FacesPerspective.z ∘ p.perspective }
  | _ => p


def addNewFaces (f: Faces) (acc: MoveParser (List Faces)) : MoveParser (List Faces) := do
  let l ← acc
  return l ++ [f]
  

def extendedMoveParser (ms: List ExtendedMoves) (acc: MoveParser (List Faces)) : MoveParser (List Faces) :=
  match ms with
  | [] => acc
  | m :: ms' => do
    if m.isFace then
      let f ← doExcept (m.toFace)
      locally (fun x => x)
        (fun p => (extendedMoveParser ms' (addNewFaces f acc)) p)
    else
      locally (·.changePerspective m)
        (fun p => (extendedMoveParser ms' acc) p)

-- should be F U D R B
#eval (extendedMoveParser [.F, .U, .x, .F, .R, .D] (pure [])) ( { } )
-- doing x three times is the inverse of x, so F and B at the end are unchanged
#eval (extendedMoveParser [.x, .U, .x, .x, .x, .F, .B] (pure [])) ( {} )



/- def extendedMoveParser (p: Perspective) (ms: List ExtendedMoves) : MoveParser Moves :=
 -   let rec helper (parsed: ReaderT Perspective (Except String) Moves): List ExtendedMoves → ReaderT Perspective (Except String) Moves
 -     | [] => pure []
 -     | m :: ms' => do
 -       /- let changedPerspective ← (Perspective.changePerspective m) <$> parsed -/
 -       /- if m.isFace then -/
 -       let newParse ← (withReader (Perspective.changePerspective m)
 -         ( parsed ))
 -       if m.isFace then
 -         let face ← (← currentPerspective).perspective <$> facesToOrientation <$> m.toFace
 -         
 -       sorry
 -         /- let move ← ([ · ]) <$> facesToOrientation <$> m.toFace -/
 -         
 -         
 -       /- else -/
 -         
 -       
 -       
 -   sorry -/
