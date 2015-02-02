open import Prelude
open import Level using (Level; _⊔_) renaming (zero to lz; suc to ls)
open import Data.Maybe using (Maybe; nothing; just)

module Utils.Monads where

  ---------------------
  -- Monad Typeclass --
  ---------------------

  record Monad {a}(M : Set a → Set a) : Set (ls a) where
    infixl 1 _>>=_
    field
      return : {A : Set a} → A → M A
      _>>=_  : {A B : Set a} → M A → (A → M B) → M B

  open Monad {{...}}

  -----------------
  -- Maybe Monad --
  -----------------

  instance
    MonadMaybe : ∀{a} → Monad {a} Maybe
    MonadMaybe = record
      { return = just
      ; _>>=_  = λ { nothing  _ → nothing 
                   ; (just x) f → f x 
                   }
      }

  -----------------
  -- State Monad --
  -----------------

  record ST (s a : Set) : Set where
    field run : s → (a × s)

  evalST : ∀{a s} → ST s a → s → a
  evalST s = p1 ∘ (ST.run s)

  get : ∀{s} → ST s s
  get = record { run = λ s → (s , s) }

  put : ∀{s} → s → ST s Unit
  put s = record { run = λ _ → (unit , s) }

  instance
    MonadState : ∀{s} → Monad (ST s)
    MonadState = record
      { return = λ a → record { run = λ s → a , s }
      ; _>>=_  = λ x f → record { run = 
                 λ s → let y = ST.run x s
                       in ST.run (f (p1 y)) (p2 y)
                }
      }

  -------------
  -- Fresh ℕ --
  -------------

  Freshℕ : Set → Set
  Freshℕ A = ST ℕ A

  runFresh : ∀{A} → Freshℕ A → A
  runFresh f = evalST f 0

  inc : Freshℕ Unit
  inc = get >>= (put ∘ suc)
