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

    unarg : {A : Set} → Arg A → A
    unarg (arg _ x) = x

  make-RWData : Name → AgTerm → List (Arg AgType) → Err StratErr RWData
  make-RWData act goal ctx with Ag2RTerm goal | Ag2RType (type act) | map (Ag2RType ∘ unarg) ctx
  ...| g' | ty | ctx' with forceBinary g' | (typeResult ty) >>= forceBinary ∘ lift-ivar id
  ...| just g | just a = return (rw-data g a ctx')
  ...| just _ | nothing = throwError (Custom "Something strange happened with ((typeResult ty) >>= forceBinary)")
  ...| nothing | just _ = throwError (Custom "Something strange happened with (forceBinary g)")
  ...| nothing | nothing = throwError (Custom "My brain just exploded.") 

  postulate
    RW-error : ∀{a}{A : Set a} → String → A

  RWerr : Name → RWData → Err StratErr AgTerm
  RWerr act d
    =   runUStrats d
    >>= runTStrats db d act
    >>= return ∘ R2AgTerm

  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  by : Name → List (Arg AgType) → AgTerm → AgTerm
  by act ctx goal with runErr (make-RWData act goal ctx >>= RWerr act)
  ...| i1 err  = RW-error err
  ...| i2 term = term

  private
    lift-ivar-rwdata : RWData → RWData
    lift-ivar-rwdata (rw-data g (hd , t1 , t2) c)
      = rw-data g (hd , lift-ivar id t1 , lift-ivar id t2) c

  by-static : Name → List (Arg AgType) → AgTerm → AgTerm
  by-static act ctx goal with runErr (make-RWData act goal ctx >>= RWerr act ∘ lift-ivar-rwdata)
  ...| i1 err  = RW-error err
  ...| i2 term = term
