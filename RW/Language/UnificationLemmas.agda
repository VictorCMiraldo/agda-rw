open import Prelude renaming (_++_ to _++-List_)
open import Data.Maybe using (Maybe; just; nothing; maybe; From-just)
open import Data.Fin using (Fin; toℕ) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; sym)
open import Algebra using (module CommutativeSemiring; module DistributiveLattice)
open import Relation.Binary using (module DecTotalOrder)
-- open import Data.Vec using (Vec) renaming ([] to []v; _∷_ to _∷v_)

open import RW.Language.RTerm

module RW.Language.UnificationLemmas where

  open import RW.Language.UnificationBase
  open import Data.List.All as A
  open import Data.List.Any as N
  open Inject {{...}}

  {-# TERMINATING #-}
  termIsClosed : {A : Set} → RTerm A → Set
  termIsClosed (ovar x) = ⊥
  termIsClosed (ivar n) = Unit
  termIsClosed (rlit l) = Unit
  termIsClosed (rlam t) = termIsClosed t
  termIsClosed (rapp n ts) = All termIsClosed ts

  finZeroIsClosed : (t : FinTerm zero) → termIsClosed t
  finZeroIsClosed (ovar ())
  finZeroIsClosed (ivar n)    = unit
  finZeroIsClosed (rlit l)    = unit
  finZeroIsClosed (rlam t)    = finZeroIsClosed t
  finZeroIsClosed (rapp n []) = []
  finZeroIsClosed (rapp n (x ∷ ts)) 
    = finZeroIsClosed x 
    ∷ finZeroIsClosed (rapp n ts)

  
  -- A closed term can be cast into anything!
  -- Even better, this anything stays closed! :)
  mutual
    cast-prf : {A B : Set}(t : RTerm A)
             → termIsClosed t
             → Σ (RTerm B) termIsClosed
    cast-prf (ovar x) ()
    cast-prf (ivar n) prf = ivar n , unit
    cast-prf (rlit l) prf = rlit l , unit
    cast-prf (rlam t) prf with cast-prf t prf
    ...| t' , prf'  = rlam t' , prf'
    cast-prf (rapp n ts) prf with cast-prf* ts prf
    ...| ts' , prf' = rapp n ts' , prf'
  
    cast-prf* : {A B : Set}(ts : List (RTerm A))
              → All termIsClosed ts
              → Σ (List (RTerm B)) (All termIsClosed)
    cast-prf* [] _ = [] , []
    cast-prf* (t ∷ ts) (p ∷ ps)
      with cast-prf t p | cast-prf* ts ps
    ...| t' , p' | ts' , ps' = t' ∷ ts' , p' ∷ ps'

  -- sometimes we don't need the proof.
  cast : {A B : Set}(t : RTerm A)
       → termIsClosed t
       → RTerm B
  cast t = p1 ∘ cast-prf t
                                                    
  -- check always returns a just on closed terms.
  -- seems very provable, although it's gonna be painful.
  checkClosed : ∀{n} → (x : Fin (suc n))(t : FinTerm (suc n))
              → (prf : termIsClosed t)
              → check x t ≡ just (cast t prf)
  checkClosed x (ovar x₁) ()
  checkClosed x (ivar n₁) prf = refl
  checkClosed x (rlit l) prf = refl
  checkClosed x (rlam t) prf = {!!}
  checkClosed x (rapp n₁ ts) prf = {!!}
                                   
  -- flexRigid always returns a just on a closed term.
  flexRigidClosed : ∀{n} → (x : Fin n)(t : FinTerm n)
                  → termIsClosed t
                  → ∃ (λ s → flexRigid x t ≡ just s)
  flexRigidClosed {zero} () t prf
  flexRigidClosed {suc n} x t prf 
      with check x t | checkClosed x t prf
  flexRigidClosed {suc n} x t prf | .(just (cast t prf)) | refl 
    = (n , snoc nil (cast t prf) x) , refl

  data CSubst : ℕ → ℕ → Set where
    nil  : ∀ {n}   → CSubst n n
    snoc : ∀ {m n} → (s : CSubst m n) → (t : FinTerm m) → termIsClosed t
         → (x : Fin (suc m)) → CSubst (suc m) n

  flexRigidC : ∀{n}(x : Fin n)(t : FinTerm n)
             → termIsClosed t
             → Maybe (∃ (CSubst n))
  flexRigidC {zero}  () t prf
  flexRigidC {suc n} x  t prf with cast-prf {B = Fin n} t prf
  ...| t' , prf' = just (n , snoc nil t' prf' x)

  mutual
    unifyAcc0 : ∀{m}(t₁ : FinTerm m)(t₂ : FinTerm zero)
              → ∃ (CSubst m) 
              → Maybe (∃ (CSubst m))
    unifyAcc0 (rlit l₁) (rlit l₂) (n , nil) with l₁ ≟-Lit l₂
    ...| yes l₁≡l₂ rewrite l₁≡l₂ = just (n , nil)
    ...| no  _     = nothing
    unifyAcc0 (rapp _ _) (rlit _)   _ = nothing
    unifyAcc0 (rapp _ _) (ivar _)   _ = nothing
    unifyAcc0 (rapp _ _) (rlam _)   _ = nothing
    unifyAcc0 (rlit _)   (ivar _)   _ = nothing
    unifyAcc0 (rlit _)   (rlam _)   _ = nothing
    unifyAcc0 (rlit _)   (rapp _ _) _ = nothing
    unifyAcc0 (rlam _)   (rapp _ _) _ = nothing
    unifyAcc0 (rlam _)   (ivar _)   _ = nothing
    unifyAcc0 (rlam _)   (rlit _)   _ = nothing
    unifyAcc0 (ivar _)   (rlit _)   _ = nothing
    unifyAcc0 (ivar _)   (rapp _ _) _ = nothing
    unifyAcc0 (ivar _)   (rlam _)   _ = nothing
    unifyAcc0 (ivar x)   (ivar y) acc with x ≟-ℕ y
    ...| yes x≡y = just acc
    ...| no  _   = nothing
    unifyAcc0 (rlam x)   (rlam y) acc = unifyAcc0 x y acc
    unifyAcc0 (rapp x ax) (rapp y ay) acc with x ≟-RTermName y
    ...| yes x≡y rewrite x≡y = unifyAcc0* ax ay acc
    ...| no  _   = nothing
    unifyAcc0 (ovar x)  (ovar ()) (n , nil)
    unifyAcc0 (ovar x)   t  (n , nil) 
      with cast-prf {B = Fin n} t (finZeroIsClosed t)
    ...| t' , prf = flexRigidC x t' prf
    unifyAcc0 t    (ovar ()) (n , nil)
    unifyAcc0 t₁ t₂ (n , snoc s t′ prf x) =
      ( λ s → p1 s , snoc (p2 s) t′ prf x )
        <$> unifyAcc0 (replace-A (t′ for x) t₁) t₂ (n , s)


    unifyAcc0* : ∀ {n} → (ts₁ : List (FinTerm n))
               → (ts₂ : List (FinTerm zero))
               → ∃ (CSubst n) → Maybe (∃ (CSubst n))
    unifyAcc0* [] [] acc = just acc
    unifyAcc0* [] _  _   = nothing
    unifyAcc0* _  [] _   = nothing
    unifyAcc0* (t ∷ ts) (u ∷ us) acc with unifyAcc0 t u acc
    ...| nothing   = nothing
    ...| just acc' = unifyAcc0* ts us acc'
