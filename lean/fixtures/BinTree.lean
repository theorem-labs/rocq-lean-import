namespace Scratch

inductive BinTree (α : Type u) where
  | leaf : α -> BinTree α
  | node : BinTree α -> BinTree α -> BinTree α

end Scratch
