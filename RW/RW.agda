{-# OPTIONS --allow-unsolved-metas  #-}
open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import Data.String using (String)

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.FinTerm
open import RW.Language.GoalGuesser

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

  -- Given a goal and a list of actions to apply to such goal, return
  -- a list l₁ ⋯ lₙ such that ∀ 0 < i ≤ n . tyᵢ : p1 lᵢ → p1 lᵢ₊₁ 
  Ag2RTypeFin* : RTerm ⊥ → List AgType → Maybe (List (RBinApp ⊥ × ∃ (RBinApp ∘ Fin)))
  Ag2RTypeFin* (rapp n (g₁ ∷ g₂ ∷ [])) tys 
    =            mapM (return ∘ Ag2RTypeFin) tys
    >>=          mapM (λ v → forceBinary (typeResult (p2 v)) >>= (return ∘ (_,_ $ p1 v)))
    >>= λ tys' → (divideGoal (n , g₁ , g₂) tys' >>= assemble)
    >>= λ gs   → return (zip gs tys')
    where
      assemble : {A : Set} → List (RTerm A) → Maybe (List (RBinApp A))
      assemble (x1 ∷ x2 ∷ []) = just ((n , x1 , x2) ∷ [])
      assemble (x1 ∷ x2 ∷ l)  = assemble (x2 ∷ l) >>= return ∘ (_∷_ (n , x1 , x2))
      assemble _              = nothing
  Ag2RTypeFin* _ _ = nothing

  make-RWData* : List Name → AgTerm → List (Arg AgType) → Err StratErr (List RWData)
  make-RWData* acts goal ctx with Ag2RTerm goal | map type acts | map (Ag2RType ∘ unarg) ctx
  ...| g' | tys | ctx' with Ag2RTypeFin* g' tys
  ...| nothing = throwError (Custom "Are you sure you can apply those steps?")
  ...| just r  = i2 (map (λ x → rw-data (p1 x) (p1 (p2 x)) (p2 (p2 x)) ctx') r)

  postulate
    RW-error : ∀{a}{A : Set a} → String → A

  RWerr : Name → RWData → Err StratErr (RWData × UData × RTerm ⊥)
  RWerr act d
    =   runUStrats d
    >>= λ u → runTStrats db d act u
    >>= λ v → return (d , u , v)

  -- A variant with less information, more suitable to be map'ed.
  RWerr-less : Name → RWData → Err StratErr (RTerm ⊥)
  RWerr-less act d = RWerr act d >>= return ∘ p2 ∘ p2

  by' : Name → List (Arg AgType) → AgTerm → (RWData × UData × RTerm ⊥)
  by' act ctx goal with runErr (make-RWData act goal ctx >>= RWerr act)
  ...| i1 err  = RW-error err
  ...| i2 term = term

  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  by : Name → List (Arg AgType) → AgTerm → AgTerm
  by act ctx goal = R2AgTerm ∘ p2 ∘ p2 $ (by' act ctx goal)

  join-tr : Name → List (RTerm ⊥) → RTerm ⊥
  join-tr _  []      = ivar 0
  join-tr tr (x ∷ l) = foldr (λ h r → rapp (rdef tr) (r ∷ h ∷ [])) x l

  by*-err : Name → List Name → List (Arg AgType) → AgTerm → Err StratErr AgTerm
  by*-err tr acts ctx goal 
    =   make-RWData* acts goal ctx 
    >>= λ l → mapM (uncurry RWerr-less) (zip acts l)
    >>= return ∘ R2AgTerm ∘ join-tr tr
    where
      unzip : {A B : Set} → List (A × B) → List A × List B
      unzip [] = [] , []
      unzip ((a , b) ∷ l) with unzip l
      ...| la , lb = a ∷ la , b ∷ lb

  by*-tactic : Set
  by*-tactic = List Name → List (Arg AgType) → AgTerm → AgTerm

  by* : Name → by*-tactic
  by* tr acts ctx goal with runErr (by*-err tr acts ctx goal)
  ...| i1 err = RW-error err
  ...| i2 res = res
