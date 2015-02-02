open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import Data.String using (String)

open import Language.RTerm
open import Language.RTermUtils
open import Language.Unification

open import Rel.Core.Equality

open import Strategy

module RW (db : TStratDB) where

  open import Utils.Monads
  open import Utils.Error
  open Monad {{...}}
  open IsError {{...}}

  -- We need to bring our instances into scope explicitely,
  -- to make Agda happy.
  private
    instance
      ErrErr   = IsError-StratErr
      ErrMonad = MonadError
      
  RWerr : Name → AgTerm → Err StratErr AgTerm
  RWerr act goal with Ag2RTerm goal | Ag2RType (type act)
  ...| g' | ty with forceBinary g' | (typeResult ty) >>= forceBinary
  ...| just g | just a
    =   runUStrats g a
    >>= uncurry (runTStrats db (p1 g) (p1 a) act)
    >>= return ∘ R2AgTerm
  ...| _ | _ = throwError (Custom "Something strange happened")

  postulate
    RW-error : ∀{a}{A : Set a} → String → A

  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  RW : Name → List (Arg AgType) → AgTerm → AgTerm
  RW act _ goal with runErr (RWerr act goal)
  ...| i1 err  = RW-error err
  ...| i2 term = term

  -- TODO: write Strategy.PropEq and Strategy.RelEq; pray ten times
  --       then compile.

  {-

  
  

  makeApp : Name → RSubst → RTerm ℕ
  makeApp act σ = rapp (rdef act) (map p2 σ)

  selectStrat : RTermName → RTermName -- We need both heads to decide what to do
              → RTerm (Maybe ℕ)       -- A term with a hole, or our abs.
              → Name                  -- Action name.
              → RSubst                -- Unification result; sorted.
              → RTerm ℕ
  selectStrat pat-≡ pat-≡ g□ act σ
    = rapp (rdef (quote cong))
           ( hole2Abs g□
           ∷ makeApp act σ
           ∷ [])
  selectStrat pat-→ pat-≡r g□ act σ
    = rapp (rdef (quote subst)) 
           ( hole2Abs g□
           ∷ rapp (rdef (quote ≡r-promote)) (makeApp act σ ∷ [])
           ∷ [])
  selectStrat _ _ _ _ _
    = error "Not yet implemented"

  RW+1 : Name → AgTerm → Maybe AgTerm
  RW+1 act goal with Ag2RTerm goal | Ag2RType (type act)
  ...| g' | ty with forceBinary g' | (typeResult ty) >>= forceBinary
  ...| just (hdₓ , g1 , g2) | just (hdₐ , ty1 , ty2)
    = let g□ = g1 ∩↑ g2
          u1 = (g□ -↓ g1) >>= (unify ty1)
          u2 = (g□ -↓ g2) >>= (unify ty2)
          σ  = μ ((_++ᵣ_ <$> u1) <*> u2)
      in (R2AgTerm ∘ selectStrat hdₓ hdₐ g□ act) <$> σ
      where
        μ : ∀{a}{A : Set a} → Maybe (Maybe A) → Maybe A
        μ (just x) = x
        μ nothing  = nothing
  ...| _ | _ = error "[RW+1] Somewthing went wrong."

  RW₀ : Name → AgTerm → AgTerm
  RW₀ act goal with RW+1 act goal
  ...| just t  = t
  ...| nothing = error "[RW] Something went wrong."

  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  RW : Name → List (Arg AgType) → AgTerm → AgTerm
  RW act _ goal = RW₀ act goal

  -}
