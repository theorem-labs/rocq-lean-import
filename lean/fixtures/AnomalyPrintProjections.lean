namespace Scratch

inductive aexp where
  | num : Nat -> aexp
  | plus : aexp -> aexp -> aexp

def aeval : aexp -> Nat
  | aexp.num n => n
  | aexp.plus a b => aeval a + aeval b

end Scratch
