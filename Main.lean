import Larc.DepthFirst




def findRange (name : String) (p : Nat → Bool) (high : Nat) : SearchT Id Nat := do
  let x ← SearchT.oneOf name (List.range high)
  guard $ p x
  pure x

def test_search : SearchT Id Nat := do
  let x ← findRange "x" (λ x => x ∈ [1, 3]) 10
  let y ← findRange "y" (λ x => x ∈ [2, 4]) 10
  guard $ x + y > 6
  pure $ x + y

def main : IO Unit :=
  IO.println $ search (test_search)
