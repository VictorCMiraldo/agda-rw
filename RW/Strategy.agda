open import Prelude
open import Data.Maybe using (Maybe; just; nothing) renaming (maybe′ to maybe)
open import Data.String

open import Language.RTerm
open import Language.RTermUtils
open import Language.Unification

-- Strategy Module.
--
--  Here we'll provide a modular approach to implementing both 
--  unification and  abstraction-guessing strategies based
--  on the head of both terms.
module Strategy where
  
  open import Utils.Monads using (module Monad)
  open import Utils.Error
  open Monad {{...}}
  open IsError {{...}}

  -------------------------
  -- Error Layer
  -------------------------

  -- Strategy related errors
  data StratErr : Set where
    Nothing       : StratErr
    NoUnification : StratErr
    NoUStrat      : StratErr
    NoTStrat      : StratErr
    Custom        : String → StratErr

  instance
    IsError-StratErr : IsError StratErr
    IsError-StratErr = record { showError = showErr }
      where
        showErr : StratErr → String
        showErr Nothing       = "Nothing; Internal msg passing flag."
        showErr NoUnification = "No unification could be performed."
        showErr NoUStrat      = "No suitable unification strategy found."
        showErr NoTStrat      = "No suitable term stragety found."
        showErr (Custom msg)  = "[!] " Data.String.++ msg

  -------------------------
  -- Unification Strategy Layer
  -------------------------

  -- A Unification strategy is meant to obtain
  -- a suitable substitution for applying the given
  -- action to the goal in question.
  --
  -- Simply unifying the goal type with the action result type
  -- does not work. They usually have non-unifiable types.
  -- They do, however, have unifiable sub-terms, which
  -- must be 'extracted' following a given strategy.
  --
  -- It is worth mentioning that these will be hardcoded
  -- and modifying the unification strategy pipeline will
  -- require recompiling the code.
  record UStrat : Set where
    field
      -- Predicate for when we should apply this strategy.
      -- First is the goal top-most name; followed by
      -- the actions top-most name.
      when : RTermName → RTermName → Bool

      -- Extract an abstraction and a substitution
      -- to be passed on to subsequent term-guessing
      -- strategy.
      howᵤ : RBinApp ℕ -- Again, Goal term opened as a binary application.
           → RBinApp ℕ -- Action term. 
           → Err StratErr (RTerm (Maybe ℕ) × RSubst)
  
  -- Basic strategy
  basicUStrat : UStrat
  basicUStrat = record
    { when = λ _ _ → true
    ; howᵤ = basic
    } where
      μ : ∀{a}{A : Set a} → Maybe (Maybe A) → Maybe A
      μ (just x) = x
      μ nothing  = nothing

      basic : RBinApp ℕ → RBinApp ℕ
            → Err StratErr (RTerm (Maybe ℕ) × RSubst)
      basic (hdₓ , g1 , g2) (hdₐ , ty1 , ty2)
        = let g□ = g1 ∩↑ g2
              u1 = (g□ -↓ g1) >>= (unify ty1)
              u2 = (g□ -↓ g2) >>= (unify ty2)
              σ  = μ ((_++ᵣ_ <$> u1) <*> u2)
        in maybe (λ s → i2 (g□ , s)) (i1 NoUnification) σ

  -- Runs the unification strategies we know about
  -- in the given target terms.
  runUStrats : RBinApp ℕ → RBinApp ℕ
             → Err StratErr (RTerm (Maybe ℕ) × RSubst)
  runUStrats
    = chose ustratDB
    where
      ustratDB : List UStrat
      ustratDB = basicUStrat ∷ []

      chose : List UStrat → RBinApp ℕ → RBinApp ℕ
            → Err StratErr (RTerm (Maybe ℕ) × RSubst)
      chose [] _ _ = i1 NoUStrat
      chose (u ∷ us) g a with UStrat.when u (p1 g) (p1 a)
      ...| false = chose us g a
      ...| true  
         = catchError (UStrat.howᵤ u g a)
                      (λ { Nothing → chose us g a
                         ; e       → i1 e
                         })
      
  
  -------------------------
  -- Term Strategy Layer
  -------------------------

  -- The Term Guessing Strategy should be plugged right after
  -- a unification has been succesfuly performed.
  -- 
  -- Given the head of both our goal and action we
  -- should be able to guess a term that 'bridges' them.
  record TStrat : Set where
    field
      when : RTermName → RTermName → Bool

      how  : Name → RTerm (Maybe ℕ) → RSubst → Err StratErr (RTerm ℕ)

  -- For now, we'll use a naive list to implement a TStrat
  -- database.
  TStratDB : Set
  TStratDB = List TStrat

  -- Utility to run a list of TStrat's.
  runTStrats : TStratDB → RTermName → RTermName
             → Name → RTerm (Maybe ℕ) → RSubst → Err StratErr (RTerm ℕ)
  runTStrats [] _ _  = λ _ _ _ → i1 NoTStrat
  runTStrats (s ∷ ss) g a with TStrat.when s g a
  ...| false = runTStrats ss g a
  ...| true  = TStrat.how s 

  -- From a name and a substitution create an application.
  makeApp : Name → RSubst → RTerm ℕ
  makeApp act σ = rapp (rdef act) (map p2 σ)
