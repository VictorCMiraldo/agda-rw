open import Prelude
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; _∷_; [])

open import RW.Language.RTerm
open import RW.Language.FinTerm
open import RW.Language.RTermUtils
open import RW.Utils.Monads

module RW.Language.GoalGuesser where
  
  open Monad {{...}}

  ----------------
  -- Housekeeping

  private
    cast-RBinApp : {A B : Set} → (A → B) → RBinApp A → RBinApp B
    cast-RBinApp f (n , a , b) = n , replace-A (ovar ∘ f) a , replace-A (ovar ∘ f) b

    RBinApp02⊥ : RBinApp (Fin zero) → RBinApp ⊥
    RBinApp02⊥ = cast-RBinApp (λ ())

    symmetric : {A : Set} → RBinApp A → RBinApp A
    symmetric (n , a , b) = n , b , a

  -----------------
  -- Term subsitution

  -- Given a RBinApp representing a type (t₁ ▵ t₂), will return a
  -- non-deterministic substitution of t₂ for t₁ in a given goal g.
  -- If no substitution could be performed, the empty list will be returned.
  _[_] : {A : Set}{{eqA : Eq A}} → RTerm A → RTerm A × RTerm A → NonDet (RTerm A)
  g [ ty1 , ty2 ] = map p2 (filter p1 (substRTermAux g ty1 ty2))  
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

  -- Given a term and a type ty with n variables, will search for n subterms of t
  -- in a non-deterministic fashion, and will instantiate them as parameters to ty.
  {-# TERMINATING #-}
  apply : {n : ℕ} → RTerm ⊥ → RBinApp (Fin n) → NonDet (RTerm ⊥)
  -- If we have no more variables to instantiate on our type,
  -- we can proceed to substitute.
  apply {n = zero}  g (_ , ty1 , ty2) 
    = g [ Fin2RTerm⊥ ty1 , Fin2RTerm⊥ ty2 ]

  -- If not, we simply call with a recursively smaller n
  apply {n = suc n} g t = inst g t >>= apply g
    where
      -- Easy way of discarding the last variable of a Fin n.
      -- Mainly, we map Fin (1 + n) to 1 + Fin n.
      thin : {n : ℕ} → Fin (suc n) → Maybe (Fin n)
      thin {zero} _       = nothing
      thin {suc n} fz     = just fz
      thin {suc n} (fs x) with thin x
      ...| nothing = nothing
      ...| just x' = just (fs x')

      -- Given a closed term t, returns a substitution σ defined
      -- by σ(n+1) = t, σ(k, k ≤ n) = var k.
      ▵_ : {n : ℕ} → RTerm ⊥ → Fin (suc n) → RTerm (Fin n)
      ▵_ {n} t x with thin x
      ...| nothing = replace-A (λ ()) t
      ...| just x' = ovar x'

      {-# TERMINATING #-}
      mk-inst-f : {n : ℕ} → RTerm ⊥ → NonDet (Fin (suc n) → RTerm (Fin n))
      mk-inst-f (ovar ())
      mk-inst-f (ivar n)    = return (▵ (ivar n))
      mk-inst-f (rlit l)    = return (▵ (rlit l))
      mk-inst-f (rlam t)    = return (▵ (rlam t)) ++ mk-inst-f t
      mk-inst-f (rapp n ts) = return (▵ (rapp n ts)) ++ concat (mapM mk-inst-f ts)

      -- Given a term t and a type with (n+1) variables, instantiate the last variable
      -- from the type with a non-deterministic subterm of t, returns the resulting type.
      inst : {n : ℕ} → RTerm ⊥ → RBinApp (Fin (suc n)) → NonDet (RBinApp (Fin n))
      inst {n} t (r , ty1 , ty2) = mk-inst-f {n} t >>= λ f → return (r , replace-A f ty1 , replace-A f ty2)


  -- TODO: Use vectors instead of lists... 

  -- Given a goal (a ▵ b) and a list of types L, try to find intermediate goals g₁⋯gₙ such
  -- that ∀n . tyₙ ∈ L ⇒ tyₙ : gₙ₋₁ → gₙ , where g₀ = a and gₖ = b.
  divideGoal : RBinApp ⊥ → List (Σ ℕ (RBinApp ∘ Fin)) → Maybe (List (RTerm ⊥))
  divideGoal (gh , g1 , g2) l = sfHead (filter chainIsValid (stepGoals g1 l))
    where
      chainIsValid : List (RTerm ⊥) → Bool
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
      stepGoals : RTerm ⊥ → List (Σ ℕ (RBinApp ∘ Fin)) → NonDet (List (RTerm ⊥))
      stepGoals g []       = return (g ∷ [])
      stepGoals g ((nₜ , t) ∷ ts) = apply g t ++ apply g (symmetric t) 
                                >>= (λ g' → stepGoals g' ts 
                                >>= return ∘ (_∷_ g))

  module Test where

    goal : RTerm ⊥
    goal = rapp (rdef (quote _≡_))
      (rapp (rdef (quote _+_)) (ivar 0 ∷ ivar 1 ∷ []) ∷
       rapp (rdef (quote _+_))
       (ivar 0 ∷
        rapp (rdef (quote _+_)) (ivar 1 ∷ rapp (rcon (quote zero)) [] ∷ [])
        ∷ [])
       ∷ [])

    binGoal : RBinApp ⊥
    binGoal = rdef (quote _≡_)
            , rapp (rdef (quote _+_)) (ivar 0 ∷ ivar 1 ∷ [])
            , rapp (rdef (quote _+_)) (ivar 0 ∷ (rapp (rdef (quote _+_)) (ivar 1 ∷ (rapp (rcon (quote zero)) []) ∷ []) ∷ []))

    +-ri : RBinApp (Fin 1)
    +-ri = rdef (quote _≡_)
         , rapp (rdef (quote _+_)) (ovar fz ∷ rapp (rcon (quote zero)) [] ∷ [])
         , ovar fz

    +-a : RBinApp (Fin 3)
    +-a = rdef (quote _≡_)
        , rapp (rdef (quote _+_)) (rapp (rdef (quote _+_)) (ovar (fs $ fs fz) ∷ ovar (fs fz) ∷ []) ∷ ovar fz ∷ [])
        , rapp (rdef (quote _+_)) (ovar (fs $ fs fz) ∷ rapp (rdef (quote _+_)) (ovar (fs fz) ∷ ovar fz ∷ []) ∷ [])


    tylist : List (Σ ℕ (RBinApp ∘ Fin))
    tylist = (1 , +-ri) ∷ (3 , +-a) ∷ []
