

inductive T where
  | a (x : Nat) : T
  | b



def eq (x y : T) : Bool :=
  match x, y with
  | .a v1, .a v2 => true
  | _, _ => false



def a := Array.mk [1, 2, 3]
def b := Array.mk [1, 2, 3]
#eval a = b
