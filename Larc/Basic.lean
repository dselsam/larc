

structure Example (α : Type) where
  train : List α
  test : List α
  deriving Repr

structure Goal (α β : Type) where
  inputs : Example α
  outputs : List β
  deriving Repr

structure Dims where
  num_rows : Nat
  num_cols : Nat
  deriving Repr

structure Grid (α : Type) where
  dims : Dims
  elements : List (List α)
  deriving Repr

def my_example : Example Nat := Example.mk [0] [5]

#eval my_example

def my_grid : Grid Nat := Grid.mk
  (dims := Dims.mk 2 2)
  (elements := [[2, 3], [4, 5]])

#eval my_grid
