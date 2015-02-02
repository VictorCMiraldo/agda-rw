open import Prelude
open import Language.RTerm
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (maybe′ to maybe)
open import Reflection using (_≟-Lit_; _≟-Name_)
open import Utils.Monads

module Language.RTermUtils where

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
  _∩_ (rlam x) (rlam y) = x ∩ y
  _∩_ _ _ = ovar nothing

  -- Lifting holes.
  --
  --  Will translate every definition with only holes as arguments
  --  into a single hole.
  {-# TERMINATING #-}
  _↑ : ∀{a}{A : Set a} → RTerm (Maybe A) → RTerm (Maybe A)
  _↑ (rapp x ax) with all isHole ax
  ...| true   = ovar nothing
  ...| false  = rapp x (map _↑ ax)
  _↑ (rlam x) = rlam (x ↑)
  _↑ t        = t

  -- It is commom to need only "linear" intersections;
  _∩↑_ : ∀{A} ⦃ eqA : Eq A ⦄ 
       → RTerm A → RTerm A → RTerm (Maybe A)
  v ∩↑ u = (v ∩ u) ↑

  -- Converting Holes to Abstractions
  --
  --  Will replace holes for "var 0", and increment every other variable.
  holeElim : ∀{a}{A : Set a} → A → (A → A) → RTerm (Maybe A) → RTerm A
  holeElim hZ hF = replace-A (maybe (ovar ∘ hF) (ovar hZ))

  -- Specialized version for handling indexes.
  hole2Abs : RTerm (Maybe ℕ) → RTerm ℕ
  hole2Abs = rlam ∘ holeElim zero suc

  -- Term Subtraction
  {-# TERMINATING #-}
  _-_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (List (RTerm A))
  hole - t = return (t ∷ [])
  (rapp x ax) - (rapp y ay) with x ≟-RTermName y
  ...| no  _ = nothing
  ...| yes _ = joinInner (map (uncurry _-_) (zip ax ay))
     where
       joinInner : ∀{A} → List (Maybe (List A)) → Maybe (List A)
       joinInner [] = return []
       joinInner (nothing ∷ _) = nothing
       joinInner (just x ∷ xs) = joinInner xs >>= return ∘ _++_ x
  (rlam x) - (rlam y) = x - y
  x - y with x ≟-RTerm (replace-A (ovar ∘ just) y)
  ...| yes _ = just []
  ...| no  _ = nothing

  -- Term Subtraction, single result.
  _-↓_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (RTerm A)
  t -↓ u with t - u
  ...| just []      = nothing
  ...| just (x ∷ _) = just x
  ...| nothing      = nothing

  -- Structural Manipulation
  
  RBinApp : ∀{a} → Set a → Set _
  RBinApp A = RTermName × RTerm A × RTerm A

  -- Opens a term representing a binary application.
  forceBinary : ∀{a}{A : Set a} 
              → RTerm A → Maybe (RBinApp A)
  forceBinary (rapp n (a₁ ∷ a₂ ∷ [])) = just (n , a₁ , a₂)
  forceBinary _                       = nothing

  -- Given a 'impl' chain, return it's result.
  typeResult : ∀{a}{A : Set a}
             → RTerm A → Maybe (RTerm A)
  typeResult (rapp impl (t1 ∷ t2 ∷ [])) = aux t2
    where
      aux : ∀{a}{A : Set a} → RTerm A → Maybe (RTerm A)
      aux (rapp impl (t1 ∷ t2 ∷ [])) = aux t2
      aux t                          = just t
  typeResult _ = nothing
