open import Prelude renaming (_++_ to _++-List_)
open import Data.Maybe using (Maybe; just; nothing; maybe; From-just)
open import Data.Fin using (Fin; toℕ) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; sym)
open import Algebra using (module CommutativeSemiring; module DistributiveLattice)
open import Relation.Binary using (module DecTotalOrder)
-- open import Data.Vec using (Vec) renaming ([] to []v; _∷_ to _∷v_)

open import RW.Language.RTerm

module RW.Language.UnificationLemmas where

  open import RW.Language.Unification
  open import Data.List.All as A
  open import Data.List.Any as N

  {-# TERMINATING #-}
  termIsClosed : {A : Set} → RTerm A → Set
  termIsClosed (ovar x) = ⊥
  termIsClosed (ivar n) = Unit
  termIsClosed (rlit l) = Unit
  termIsClosed (rlam t) = termIsClosed t
  termIsClosed (rapp n ts) = All termIsClosed ts

  -- Proof idea:
  --
  --  1. Define a subterm relation; it must be transitive.
  --  2. Prove that if a ≤ b, for a closed term b,
  --  then a must also be closed.
  --  3. Prove that unification returns subterms of either t1 or t2.
  --  4. If t1 is closed, unification returns subterms of t1
  --  5. Unification results are also closed.

  module Subterm (A : Set) ⦃ eq : Eq A ⦄ where
    open import Relation.Binary.PropositionalEquality renaming (setoid to ≡-setoid)
    open N.Membership (≡-setoid (RTerm A)) using (_∈_)

    Term : Set
    Term = RTerm A

    mutual
      data _≤*_ : List Term → List Term → Set where
        ≤*-nil : ∀{us}                           → []       ≤* us
        ≤*-sub : ∀{t u ts us} → t ≤ u → ts ≤* us → (t ∷ ts) ≤* (u ∷ us)  
  
      -- Subterm relation
      data _≤_ : Term → Term → Set where
        ≤-refl  : ∀{t}      → t ≤ t
        ≤-lam   : ∀{t u}    → t ≤ u → t ≤ (rlam u)
        ≤-rapp1 : ∀{t ts n} → Any (λ v → t ≤ v) ts
                            → t ≤ (rapp n ts)
        ≤-rapp2 : ∀{t ts n} → t ≤* ts 
                            → rapp n t ≤ rapp n ts

    {-# TERMINATING #-}
    lam-≤ : {a b : Term} → rlam a ≤ b → a ≤ b
    lam-≤ ≤-refl      = ≤-lam ≤-refl
    lam-≤ (≤-lam prf) = ≤-lam (lam-≤ prf)
    lam-≤ (≤-rapp1 x) = ≤-rapp1 (N.map lam-≤ x)

    rapp-≤-refl : ∀{n}{bs : List Term}
                → All (λ b → b ≤ (rapp n bs)) bs
    rapp-≤-refl = {!!}
      where
        rapp-drop-head : ∀{n}{x b : Term}{bs : List Term}
                       → x ≤ rapp n bs → x ≤ rapp n (x ∷ bs)
        rapp-drop-head ≤-refl = ≤-rapp1 (here ≤-refl)
        rapp-drop-head (≤-rapp1 x) = ≤-rapp1 (here ≤-refl)
        rapp-drop-head (≤-rapp2 x) = ≤-rapp1 (here ≤-refl)

    rapp-≤ : ∀{n}{a : Term}{bs : List Term}
           → rapp n bs ≤ a → All (λ b → b ≤ a) bs
    rapp-≤ {n} {a = .(rapp _ _)} ≤-refl = rapp-≤-refl
    rapp-≤ {bs = []} (≤-lam prf) = []
    rapp-≤ {bs = x ∷ bs} (≤-lam prf) = {!!}
    rapp-≤ (≤-rapp1 x) = {!!}
    rapp-≤ (≤-rapp2 x) = {!!}