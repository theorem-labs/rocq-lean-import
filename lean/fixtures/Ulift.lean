namespace Scratch

inductive MyNat : Type where
  | zero : MyNat

inductive MyProd (α : Sort u) (β : Sort v) : Sort (max u v) where
  | mk : α -> β -> MyProd α β

def example1 : MyProd (ULift.{1, 0} MyNat) Type :=
  MyProd.mk (ULift.up MyNat.zero) Type

def useUp.{u} (α : Type u) (x : α) : ULift.{u, u} α :=
  ULift.up x

end Scratch
