{-# OPTIONS --allow-unsolved-metas  #-}
open import Prelude
open import Data.Nat using (_≤?_)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (maybe′ to maybe)
open import Reflection using (_≟-Lit_; _≟-Name_)

open import RW.Language.RTerm
open import RW.Utils.Monads

module RW.Language.RTermUtils where

  open Monad {{...}}

  -------------------------------------------------------
  -- Terms with Context
  --
  --   Holes will be represented by a nothing;
  pattern hole = ovar nothing

  isHole : ∀{a}{A : Set a} → RTerm (Maybe A) → Bool
  isHole (ovar nothing) = true
  isHole _              = false

  -- Term Intersection
  --
  {-# TERMINATING #-}
  _∩_ : ∀{A} ⦃ eqA : Eq A ⦄ 
      → RTerm A → RTerm A → RTerm (Maybe A)
  _∩_ (rapp x ax) (rapp y ay) with x ≟-RTermName y
  ...| no  _ = ovar nothing
  ...| yes _ = rapp x (map (uncurry _∩_) (zip ax ay))
  _∩_ (ivar x) (ivar y) with x ≟-ℕ y
  ...| no  _ = ovar nothing
  ...| yes _ = ivar x
  _∩_ ⦃ eq f ⦄ (ovar x) (ovar y) with f x y
  ...| no  _ = ovar nothing
  ...| yes _ = ovar (just x)
  _∩_ (rlit x) (rlit y) with x ≟-Lit y
  ...| no  _ = ovar nothing
  ...| yes _ = rlit x
  _∩_ (rlam x) (rlam y) = rlam (x ∩ y)
  _∩_ _ _ = ovar nothing

  -- Lifting holes.
  --
  --  Will translate every definition with only holes as arguments
  --  into a single hole.
  {-# TERMINATING #-}
  _↑ : ∀{a}{A : Set a} → RTerm (Maybe A) → RTerm (Maybe A)
  _↑ (rapp x []) = rapp x []
  _↑ (rapp x ax) with all isHole ax
  ...| true   = ovar nothing
  ...| false  = rapp x (map _↑ ax)
  _↑ (rlam x) = rlam (x ↑)
  _↑ t        = t

  -- It is commom to need only "linear" intersections;
  _∩↑_ : ∀{A} ⦃ eqA : Eq A ⦄ 
       → RTerm A → RTerm A → RTerm (Maybe A)
  v ∩↑ u = (v ∩ u) ↑

  -- Casting
  ⊥2UnitCast : RTerm (Maybe ⊥) → RTerm Unit
  ⊥2UnitCast = replace-A (maybe ⊥-elim (ovar unit))

  -- Converting Holes to Abstractions
  --
  --  Will replace holes for "var 0", and increment every other variable.
  {-# TERMINATING #-}
  holeElim : ℕ → RTerm Unit → RTerm ⊥
  holeElim d (ovar unit) = ivar zero
  holeElim d (ivar n) with suc n ≤? d
  ...| yes _ = ivar n
  ...| no  _ = ivar (suc n)
  holeElim d (rlit l) = rlit l
  holeElim d (rlam rt) = rlam (holeElim (suc d) rt)
  holeElim d (rapp n ts) = rapp n (map (holeElim d) ts)

  -- Specialized version for handling indexes.
  hole2Abs : RTerm Unit → RTerm ⊥
  hole2Abs = rlam ∘ holeElim 0

  hole2Absℕ : RTerm Unit → RTerm ℕ
  hole2Absℕ = replace-A ⊥-elim ∘ hole2Abs

  open import Data.String hiding (_++_)
  postulate
    err : ∀{a}{A : Set a} → String → A

  -- Term Subtraction
  {-# TERMINATING #-}
  _-_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (List (RTerm A))
  hole - t = return (t ∷ [])
  (rapp x ax) - (rapp y ay) with x ≟-RTermName y
  ...| no  _ = err "1" -- nothing
  ...| yes _ = joinInner (map (uncurry _-_) (zip ax ay))
     where
       joinInner : ∀{A} → List (Maybe (List A)) → Maybe (List A)
       joinInner [] = return []
       joinInner (nothing ∷ _) = err "2" -- nothing
       joinInner (just x ∷ xs) = joinInner xs >>= return ∘ _++_ x
  (rlam x) - (rlam y) = x - y
  x - y with x ≟-RTerm (replace-A (ovar ∘ just) y)
  ...| yes _ = just []
  ...| no  _ = err "3" -- nothing

  -- Term Subtraction, single result.
  _-↓_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (RTerm A)
  t -↓ u with t - u
  ...| just []      = nothing
  ...| just (x ∷ _) = just x
  ...| nothing      = nothing

  -- Structural Manipulation

  {-# TERMINATING #-}
  lift-ivar' : ℕ → RTerm ⊥ → RTerm ℕ
  lift-ivar' _ (ovar ())
  lift-ivar' d (ivar n) with d ≤? n
  ...| yes _ = ovar n
  ...| no  _ = ivar n
  lift-ivar' _ (rlit l) = rlit l
  lift-ivar' d (rlam t) = rlam (lift-ivar' (suc d) t)
  lift-ivar' d (rapp n ts) = rapp n (map (lift-ivar' d) ts)
  
  -- Lift ivar's to ovar's
  lift-ivar : RTerm ⊥ → RTerm ℕ
  lift-ivar = lift-ivar' 0
  
  -- Models a binary application
  RBinApp : ∀{a} → Set a → Set _
  RBinApp A = RTermName × RTerm A × RTerm A

  -- Opens a term representing a binary application.
  forceBinary : ∀{a}{A : Set a} 
              → RTerm A → Maybe (RBinApp A)
  forceBinary (rapp n (a₁ ∷ a₂ ∷ [])) = just (n , a₁ , a₂)
  forceBinary _                       = nothing

  -- Given a 'impl' chain, return it's result.
  typeResult : ∀{a}{A : Set a}
             → RTerm A → RTerm A
  typeResult (rapp impl (t1 ∷ t2 ∷ [])) = typeResult t2
  typeResult t = t

  -- Gives the length of a 'impl' chain.
  typeArity : ∀{a}{A : Set a} → RTerm A → ℕ
  typeArity (rapp impl (t1 ∷ t2 ∷ [])) = suc (typeArity t2)
  typeArity _                          = 0
