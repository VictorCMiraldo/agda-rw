open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String renaming (_++_ to _++s_)

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.FinTerm
open import RW.Language.Instantiation 

-- Strategy Module.
--
--  Here we'll provide a modular approach to implementing both 
--  unification and  abstraction-guessing strategies based
--  on the head of both terms.
module RW.Strategy where
  
  --   The complexity annotations might require 
  --   a slight notational introduction.
  --
  --   If a variable name overlaps one in the corresponding type signature,
  --   this is intentional.
  --
  --   Sₜ is defined by (S t).
  --   #Fvₜ is defined by length (Fv t).
  --   Both measures are defined at RW.Language.RTermUtils.
  --

  open import RW.Utils.Monads using (module Monad)
  open import RW.Utils.Error
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
    NoTStrat      : RTermName → RTermName → StratErr
    Custom        : String → StratErr

  instance
    IsError-StratErr : IsError StratErr
    IsError-StratErr = record { showError = showErr }
      where
        showErr : StratErr → String
        showErr Nothing        = "Nothing; Internal msg passing flag."
        showErr NoUnification  = "No unification could be performed."
        showErr NoUStrat       = "No suitable unification strategy found."
        showErr (NoTStrat g a) = "No suitable term stragety found.\n" 
                              ++s showRTermName g ++s ", " ++s showRTermName a
        showErr (Custom msg)   = "[!] " Data.String.++ msg

  -------------------------
  -- Strategy Pipeline
  --
  --  Whenever we want to perform a rewrite, we'll have a goal and an action to perform on a "subgoal"
  --  This subgoal has to figured out by us, which we denote by g□.
  --  Afterwards, we need to somehow apply our action.

  -- Let's encapsulate everything we need in a record
  record RWData : Set where
    constructor rw-data
    field 
      goal   : RBinApp ⊥
      actℕ   : ℕ
      act    : RBinApp (Fin actℕ)
      ctx    : List (RTerm ⊥)
    
    goal-name : RTermName
    goal-name = p1 goal

    goal-1 : RTerm ⊥
    goal-1 = p1 (p2 goal)
    goal-2 : RTerm ⊥
    goal-2 = p2 (p2 goal)

    act-name : RTermName
    act-name = p1 act

  open RWData

  -- We might need a few transformations here and there.
  data Trs : Set where
    Symmetry : Trs

  -- Unification data
  record UData : Set where
    constructor u-data
    field
      -- We should have an abstraction available,
      □ : RTerm Unit

      -- A substitution
      σ : RSubst
      
      -- Our action and a few transformations that might need to be applied.
      trs : List Trs

  -------------------------
  -- Unification Strategy Layer
  -------------------------

  private
    μ : ∀{a}{A : Set a} → Maybe (Maybe A) → Maybe A
    μ (just x) = x
    μ nothing  = nothing

  -- Alternatives
  infixr 4 _<|>_
  _<|>_ : ∀{a b}{A : Set a}{B E : Set b} ⦃ isErr : IsError E ⦄ 
        → (A → Err E B) → (A → Err E B)
        → A → Err E B
  (f <|> g) a with f a
  ...| i1 _ = g a
  ...| i2b  = i2b

  try-all : ∀{a b}{A : Set a}{B E : Set b} ⦃ isErr : IsError E ⦄
          → (A → Err E B) → E → List A → Err E B
  try-all f e [] = i1 e
  try-all f e (a ∷ as) with f a
  ...| i1 _ = try-all f e as
  ...| i2 r = return r

  -- Basic unification strategy
  -- 
  --  g□ ← g₁ ∩↑ g₂    ∈ O(min(Sg₁, Sg₂))
  --  t1 ← g□ -↓ g₁    ∈ O(# Fv g□)
  --  u1 ← inst ty1 t1 ∈ O(ty1n² + (Sty1 + 1) × ty1n + Sty1)
  --  t2 ← g□ -↓ g₂    ∈ O(# Fv g□)
  --  u2 ← inst ty2 t2 ∈ O(ty2n² + (Sty2 + 1) × ty2n + Sty2)
  --
  --  Summing everything up and symplifying a bit, we get:
  --  (Note that S ty = S t₁ + S t₂ + 1)
  --
  --  min(Sg₁, Sg₂) + 2 #(Fv g□) + t₁² + t₂² + Sty₁ ty₁ + Sty2 ty₂ 
  --                                                    + t₁ + t₂ + ST - 1
  --
  --  Yet, g□, ideally is our context, with one hole, since
  --  we are doing one rewrite at a time. Therefore #Fv g□ = 1. 
  --  Prunning out this constant we get:
  --
  --  min(Sg₁, Sg₂) + t₁² + t₂² + Sty₁ ty₁ + Sty2 ty₂ + t₁ + t₂ + ST
  --
  --  wlog, let us assume that t₁ ≥ t₂ and Sty1 ≥ Sty2.
  --  So,
  --      2t₁² + 2S₁t₁ + 2t₁ + 2S₁ 
  --         ≥ t₁² + t₂² + Sty₁ ty₁ + Sty2 ty₂ + t₁ + t₂ + ST
  --
  --  Also ignoring min(Sg₁, Sg₂), since it can be seen as a constant,
  --  Our basic unification strategy is somewhere around:
  -- 
  --  basic ∈ O(2t(t + S + 1) + 2S), for t = max(t₁ , t₂) 
  --                                 and S = max(St₁ , St₂) 
  -- 
  --  Which was expected! Our RTermUtils functions are linear in some of
  --  the parameters that appeared here, and instantiation was the 
  --  only quadratic one, on the number of free variables to instantiate.
  --  
  basic : RWData → Err StratErr UData
  basic (rw-data (hdₓ , g1 , g2) zero (hdₐ , ty1 , ty2) _ )
    = let g□ = g1 ∩↑ g2
      in i2 (u-data (⊥2UnitCast g□) [] [])
  basic (rw-data (hdₓ , g1 , g2) tn (hdₐ , ty1 , ty2)  _ )
    = let g□ = g1 ∩↑ g2
          u1 = (g□ -↓ g1) >>= (inst ty1)
          u2 = (g□ -↓ g2) >>= (inst ty2)
          σ  = μ ((_++ₓ_ <$> u1) <*> u2)
    in maybe (λ s → i2 (u-data (⊥2UnitCast g□) s [])) (i1 NoUnification) (σ >>= X2RSubst)
  

  -- Unification over the symmetric action type.
  basic-sym : RWData → Err StratErr UData
  basic-sym (rw-data (hdₓ , g1 , g2) tn (hdₐ , ty1 , ty2) _ )
    = let g□ = g1 ∩↑ g2 
          u1 = (g□ -↓ g1) >>= (inst ty2)
          u2 = (g□ -↓ g2) >>= (inst ty1)
          σ  = μ ((_++ₓ_ <$> u1) <*> u2)
    in maybe (λ s → i2 (u-data (⊥2UnitCast g□) s (Symmetry ∷ []))) (i1 NoUnification) (σ >>= X2RSubst)
      
  -- Runs the unification strategies we know about
  -- in the given target terms.
  runUStrats : RWData → Err StratErr UData
  runUStrats = basic <|> basic-sym 
  
  -------------------------
  -- Term Strategy Layer
  -------------------------

  -- The Term Guessing Strategy should be plugged right after
  -- a unification has been succesfuly performed.
  -- 
  -- Given the head of both our goal and action we
  -- should be able to guess a term that 'bridges' them.
  -- 
  record TStrat : Set where
    field
      when : RTermName → RTermName → Bool

      how  : Name → UData → Err StratErr (RTerm ⊥)

  -- For now, we'll use a naive list to implement a TStrat
  -- database.
  TStratDB : Set
  TStratDB = List TStrat

  -- Utility to run a list of TStrat's.
  -- Not only returns the resulting term, but also the selected TStrat.
  runTStrats : TStratDB → RWData → Name → UData → Err StratErr (RTerm ⊥)
  runTStrats [] rw = λ _ _ → i1 (NoTStrat (goal-name rw) (act-name rw))
  runTStrats (s ∷ ss) rw with TStrat.when s (goal-name rw) (act-name rw)
  ...| false = runTStrats ss rw
  ...| true  = TStrat.how s

  -- From a name and a substitution create an application.
  makeApp : Name → RSubst → RTerm ⊥
  makeApp act σ = rapp (rdef act) (map p2 σ)
