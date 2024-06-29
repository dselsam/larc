import Larc.SearchT
import Lean.Data.RBMap
import Lean

open Lean

variable {m : Type → Type} [Monad m]

abbrev History : Type := List (String × Nat)

structure Context : Type where


structure Continuation (m : Type → Type) (α : Type) : Type where
  ψ : SearchT m α
  history : History

structure SearchState (m : Type → Type) (α : Type) : Type where
  stack : List (Continuation m α) := []
  guesses : List (α × History) := []

abbrev BestFirstM (m : Type → Type) (α : Type) : Type → Type := ExceptT String (ReaderT Context (StateT (SearchState m α) m))

@[inline]
private def push (ρ : Continuation m α) : BestFirstM m α Unit :=
  modifyGet $ λ φ => ((), { φ with stack :=  ρ::φ.stack })


@[inline]
private def pop : BestFirstM m α (Option (Continuation m α)) := do
  let φ ← get
  match φ.stack with
  | [] => pure none
  | ρ::ρs =>
    modify $ λ φ => { φ with stack := ρs }
    pure $ some ρ


@[specialize]
partial def searchAux : Unit → BestFirstM m α (List (α × History)) | _ => do
  let ρ ← pop
  match ρ with
  | none =>
    let φ ← get
    pure φ.guesses
  | some (Continuation.mk ψ history) =>
    let result ← ↑(SearchT.unpack ψ)
    match result with
    | SearchResult.fail => searchAux ()
    | SearchResult.done guess => do
      modify $ λ φ => { φ with guesses := (guess, history) :: φ.guesses }
      searchAux ()
    | SearchResult.choice name choices =>
      modify $ λ φ => { φ with stack := List.map (λ ⟨index, ⟨choice⟩⟩ => ⟨choice, (name, index)::history⟩) (List.enum choices) ++ φ.stack}
      searchAux ()


@[inline]
def search (ψ : SearchT m α) : m (Except String (List (α × History))) := do
  let ctx : Context := {}
  let s   : SearchState m α := {}
  let ⟨ex, _⟩ ← (push (Continuation.mk ψ []) *> searchAux ()).run ctx s;
  pure ex
