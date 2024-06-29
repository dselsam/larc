

structure Choice (α : Type) where
  value : α

inductive SearchResult (α β : Type)
| fail
| done (guess : α)
| choice (name : String) (choices : List (Choice β))
deriving Inhabited

inductive SearchT (m : Type → Type) (α : Type) : Type
| mk : m (SearchResult α NonScalar) → SearchT m α


namespace SearchT

variable {m : Type → Type} [Monad m]

def _pure {α : Type} (guess : α) : SearchT m α :=
  SearchT.mk (pure (SearchResult.done guess))


unsafe def _bindUnsafe {α β : Type} : SearchT m α → (α → SearchT m β) → SearchT m β
| SearchT.mk f, ψ₂ =>
  SearchT.mk $ bind f $ λ (result : SearchResult α NonScalar) =>
    let result : SearchResult α (SearchT m α) := unsafeCast result;
    match result with
    | SearchResult.fail => pure SearchResult.fail
    | SearchResult.done guess => match ψ₂ guess with | SearchT.mk r => r
    | SearchResult.choice name cs =>
      pure $ SearchResult.choice name $ cs.map $ λ ⟨ψₖ⟩ =>
      let ψₖ : SearchT m β := _bindUnsafe ψₖ ψ₂;
      Choice.mk (unsafeCast ψₖ)

@[implemented_by _bindUnsafe]
opaque _bind {α β : Type} : SearchT m α → (α → SearchT m β) → SearchT m β :=
λ _ _ => SearchT.mk $ pure SearchResult.fail


instance : Monad (SearchT m) where
  pure := _pure
  bind := _bind

unsafe def choiceUnsafe (name : String) (cs : List (Choice (SearchT m α))) : SearchT m α :=
  let result : SearchResult α (SearchT m α) := SearchResult.choice name cs
  SearchT.mk $ pure (unsafeCast result)

@[implemented_by choiceUnsafe]
opaque choice (name : String) : List (Choice (SearchT m α)) → SearchT m α :=
  λ _ => SearchT.mk $ pure $ SearchResult.choice name []

def fail : SearchT m α :=
  SearchT.mk $ pure $ SearchResult.fail

unsafe def unpackUnsafe {α : Type} {m : Type → Type} [Monad m]: SearchT m α → m (SearchResult α (SearchT m α))
| SearchT.mk x => unsafeCast x

@[implemented_by unpackUnsafe]
opaque unpack {α : Type} {m : Type → Type} [Monad m] : SearchT m α → m (SearchResult α (SearchT m α))

instance : Alternative (SearchT m) where
  failure := fail
  orElse ψ₁ ψ₂ := choice "<|>" [⟨ψ₁⟩, ⟨ψ₂ ()⟩]

def oneOf (name : String) (options : List α) : SearchT m α :=
  SearchT.choice name $ options.map (λ x => ⟨pure x⟩)

end SearchT
