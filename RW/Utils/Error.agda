open import Prelude
open import RW.Utils.Monads

-- Some Error monad utilities, a là Haskell.
module RW.Utils.Error where

  open import Data.String
  
  open Monad {{...}}

  -- Error Typeclass
  record IsError {a}(A : Set a) : Set a where
    field
      showError : A → String

  open IsError {{...}}

  instance
    IsError-String : IsError String
    IsError-String = record { showError = λ s → s }

  -- Error Monad
  Err : ∀{a} → (E : Set a) ⦃ isErr : IsError E ⦄ 
             → Set a → Set a
  Err e a = e ⊎ a

  throwError : ∀{a}{E A : Set a} ⦃ isErr : IsError E ⦄
             → E → Err E A
  throwError = i1

  catchError : ∀{a}{E A : Set a} ⦃ isErr : IsError E ⦄
             → Err E A → (E → Err E A) → Err E A
  catchError (i2 a) _ = i2 a
  catchError (i1 e) f = f e 
  
  instance
    MonadError : ∀{e}{E : Set e} ⦃ isErr : IsError E ⦄
               → Monad (Err E)
    MonadError = record
      { return = i2
      ; _>>=_  = λ { (i1 err) _ → i1 err 
                   ; (i2 x  ) f → f x
                   }
      }

  runErr : ∀{a}{E A : Set a} ⦃ isErr : IsError E ⦄ 
         → Err E A → String ⊎ A
  runErr (i2 a) = i2 a
  runErr ⦃ s ⦄ (i1 e) = i1 (IsError.showError s e)
