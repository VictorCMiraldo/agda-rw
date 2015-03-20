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


  -----------------
  -- Term subsitution

  -- Given a RBinApp representing a type (t₁ ▵ t₂), will return a
  -- non-deterministic substitution of t₂ for t₁ in a given goal g.
  -- If no substitution could be performed, the empty list will be returned.
  _[_] : {A : Set}{{eqA : Eq A}} → RTerm A → RBinApp A → NonDet (RTerm A)
  g [ (_ , ty1 , ty2) ] = map p2 (filter p1 (substRTermAux g ty1 ty2))  
    where
      -- Non-deterministic term substitution. Possibly empty substitution.
      -- Since we're only interested in the situations where a single substitution is performed,
      -- we also return a boolean flag indicating whether or not we already had a substitution.
      substRTermAux : {A : Set}{{ eqA : Eq A }} → RTerm A → RTerm A → RTerm A → NonDet (Bool × RTerm A)
      substRTermAux {A} {{eqA}} t m n with t ≟-RTerm m
      ...| yes _ = return (true , n)
      ...| no  _ = substStep t m n
        where
          mutual
            substStep : RTerm A → RTerm A → RTerm A → NonDet (Bool × RTerm A)
            substStep (ovar x) _ _ = return (false , ovar x)
            substStep (ivar n) _ _ = return (false , ivar n)
            substStep (rlit l) _ _ = return (false , rlit l)
            substStep (rlam t) m n = substRTermAux t m n >>= return ∘ (λ p → p1 p , rlam (p2 p))
            substStep (rapp a as) m n = substStep* as m n >>= return ∘ (λ p → p1 p , rapp a (p2 p))

            -- For the list scenario, in the inductive step, we need to substitute m for n in x,
            -- and return either the result of such substitution or the result of substituting
            -- m for n recursively in la. Do not forget that _++_ is mplus for the list monad.
            substStep* : List (RTerm A) → RTerm A → RTerm A → NonDet (Bool × List (RTerm A))
            substStep* [] _ _         = return (false , [])
            substStep* (x ∷ la) m n
              = substRTermAux x m n >>= λ x' → return (p1 x' , (p2 x' ∷ la)) 
                                            ++ (substStep* la m n >>= return ∘ (λ p → p1 p , x ∷ p2 p))

  -- Given a goal (a ▵ b) and a list of types L, try to find intermediate goals g₁⋯gₙ such
  -- that ∀n . tyₙ ∈ L ⇒ tyₙ : gₙ₋₁ → gₙ , where g₀ = a and gₖ = b.
  divideGoal : {A : Set}{{eqA : Eq A}} → RBinApp A → List (RBinApp A) → Maybe (List (RTerm A))
  divideGoal {A = A} (gh , g1 , g2) l = sfHead (filter chainIsValid (stepGoals g1 l))
    where
      chainIsValid : List (RTerm A) → Bool
      chainIsValid [] = false
      chainIsValid (x ∷ []) with x ≟-RTerm g2
      ...| yes _ = true
      ...| no  _ = false
      chainIsValid (x ∷ l) = chainIsValid l

      sfHead : {A : Set} → List A → Maybe A
      sfHead [] = nothing
      sfHead (x ∷ _) = just x

      -- Given a list of types, will return a possible list of goals that
      -- could be discharged by those types.
      stepGoals : {A : Set}{{eqA : Eq A}} → RTerm A → List (RBinApp A) → NonDet (List (RTerm A))
      stepGoals g []       = return (g ∷ [])
      stepGoals g (t ∷ ts) = g [ t ] >>= (λ g' → stepGoals g' ts >>= return ∘ (_∷_ g))

  {-
  mygoal : RBinApp ⊥
  mygoal = (impl , rapp impl (ivar 0 ∷ ivar 0 ∷ []) , rlam (ivar 2))

  tn→lamn : ℕ → RBinApp ⊥
  tn→lamn n = (impl , ivar n , rlam (ivar n))

  tn→m→k : ℕ → ℕ → ℕ → RBinApp ⊥
  tn→m→k m n k = (impl , rapp impl (ivar m ∷ ivar n ∷ []) , ivar k )

  tn→n+1 : ℕ → RBinApp ⊥
  tn→n+1 n = (impl , ivar n , ivar (suc n) )
  -}
