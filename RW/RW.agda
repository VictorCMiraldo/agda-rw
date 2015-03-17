open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import Data.String using (String)

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.FinTerm

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

  -- We need to translate types to FinTerms, so we know how many variables
  -- we're expecting to guess from instantiation.
  Ag2RTypeFin : AgType → ∃ FinTerm
  Ag2RTypeFin = R2FinType ∘ lift-ivar ∘ Ag2RType

  -- TODO: fix the duality: "number of ivar's lifted to ovar's vs. parameters we need to guess"

  make-RWData : Name → AgTerm → List (Arg AgType) → Err StratErr RWData
  make-RWData act goal ctx with Ag2RTerm goal | Ag2RTypeFin (type act) | map (Ag2RType ∘ unarg) ctx
  ...| g' | tyℕ , ty | ctx' with forceBinary g' | forceBinary (typeResult ty)
  ...| just g | just a = return (rw-data g tyℕ a ctx')
  ...| just _ | nothing = throwError (Custom "Something strange happened with the action")
  ...| nothing | just _ = throwError (Custom "Something strange happened with the goal")
  ...| nothing | nothing = throwError (Custom "My brain just exploded.") 

  postulate
    RW-error : ∀{a}{A : Set a} → String → A

  RWerr : Name → RWData → Err StratErr (RWData × UData × RTerm ⊥)
  RWerr act d
    =   runUStrats d
    >>= λ u → runTStrats db d act u
    >>= λ v → return (d , u , v)

  by' : Name → List (Arg AgType) → AgTerm → (RWData × UData × RTerm ⊥)
  by' act ctx goal with runErr (make-RWData act goal ctx >>= RWerr act)
  ...| i1 err  = RW-error err
  ...| i2 term = term

  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  by : Name → List (Arg AgType) → AgTerm → AgTerm
  by act ctx goal = R2AgTerm ∘ p2 ∘ p2 $ (by' act ctx goal)
