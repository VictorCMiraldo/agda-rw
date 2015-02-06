open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import Data.String using (String)

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.Unification

open import RW.Strategy

module RW.RW (db : TStratDB) where

  open import RW.Utils.Monads
  open import RW.Utils.Error
  open Monad {{...}}
  open IsError {{...}}

  -- We need to bring our instances into scope explicitely,
  -- to make Agda happy.
  private
    instance
      ErrErr   = IsError-StratErr
      ErrMonad = MonadError


  RWerr-final : Name → RBinApp ℕ → RBinApp ℕ → Err StratErr AgTerm
  RWerr-final act g a
    =   runUStrats g a
    >>= uncurry (runTStrats db (p1 g) (p1 a) act)
    >>= return ∘ R2AgTerm

  RWerr : Name → AgTerm → Err StratErr AgTerm
  RWerr act goal with Ag2RTerm goal | Ag2RType (type act)
  ...| g' | ty with forceBinary g' | (typeResult ty) >>= forceBinary
  ...| just g | just a = RWerr-final act g a
  ...| just _ | nothing = throwError (Custom "Something strange happened with ((typeResult ty) >>= forceBinary)")
  ...| nothing | just _ = throwError (Custom "Something strange happened with (forceBinary g)")
  ...| nothing | nothing = throwError (Custom "My brain just exploded.") 

  RWerr-static : Name → AgTerm → Err StratErr AgTerm
  RWerr-static act goal with Ag2RTerm goal | Ag2RType (type act)
  ...| g' | ty with forceBinary g' | (typeResult ty) >>= forceBinary ∘ (lift-ivar id)
  ...| just g | just a = RWerr-final act g a
  ...| just _ | nothing = throwError (Custom "Something strange happened with ((typeResult ty) >>= forceBinary)")
  ...| nothing | just _ = throwError (Custom "Something strange happened with (forceBinary g)")
  ...| nothing | nothing = throwError (Custom "My brain just exploded.") 

  postulate
    RW-error : ∀{a}{A : Set a} → String → A

  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  by : Name → List (Arg AgType) → AgTerm → AgTerm
  by act _ goal with runErr (RWerr act goal)
  ...| i1 err  = RW-error err
  ...| i2 term = term

  by-static : Name → List (Arg AgType) → AgTerm → AgTerm
  by-static act _ goal with runErr (RWerr-static act goal)
  ...| i1 err  = RW-error err
  ...| i2 term = term
