open import Prelude renaming (_++_ to _++-List_)
open import Data.Maybe using (Maybe; just; nothing; maybe; From-just)
open import Data.Fin using (Fin; toℕ) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Data.List.All as A

open import Data.Nat renaming (decTotalOrder to decTotalOrder-ℕ)
open import Relation.Binary using (module DecTotalOrder)

-- Here we provide a single-way unification, that is,
-- (unify t₁ t₂) will be 'driven' by t₁, since t₂ has
-- no variables.
--
-- Some major adaptations to RW.Language.UnificationBase were
-- made in order to guarantee that unification, when applied
-- to a closed term, returns a substitution whose image
-- is comprised only by closed terms.
--
-- RW.Language.UnificationBase module was kept in the library
-- to keep things generic, and to provide a 'two-way'
-- unification algorithm if that's needed.
--
-- The advantage of using such module is that we can also prove
-- that the resulting term is closed, making things much simpler
-- for whoever needs to develop a interface.
--
module RW.Language.Unification where

  open import RW.Language.RTerm
  open import RW.Language.UnificationBase 
    using (FinTerm; _<$>_; _<*>_; _for_; R2FinTerm)
    public

  open DecTotalOrder decTotalOrder-ℕ using (total)

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

  -- Subst datatype, borrowed from `RW.Language.UnificationBase`,
  -- with some additional information. All substitutions
  -- images are closed terms.
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

  unifyFin0 : ∀{m}(t₁ : FinTerm m)(t₂ : FinTerm zero) → Maybe (∃ (CSubst m))
  unifyFin0 {m} t₁ t₂ = unifyAcc0 t₁ t₂ (m , nil)

  --------------------------------------------------------
  -- Interface to RTerm ℕ

  -- Casting of (RTerm ⊥) to FinTerm
  mutual
    ⊥2FinTerm : RTerm ⊥ → FinTerm zero
    ⊥2FinTerm (ovar ())
    ⊥2FinTerm (ivar n) = ivar n
    ⊥2FinTerm (rlit l) = rlit l
    ⊥2FinTerm (rlam t) = rlam (⊥2FinTerm t)
    ⊥2FinTerm (rapp n ts) = rapp n (⊥2FinTerm* ts)
    
    ⊥2FinTerm* : List (RTerm ⊥) → List (FinTerm zero)
    ⊥2FinTerm* []       = []
    ⊥2FinTerm* (x ∷ xs) = ⊥2FinTerm x ∷ ⊥2FinTerm* xs
  
  RSubst : Set
  RSubst = List (ℕ × RTerm ⊥)

  private
    projSubst : ∀{n m} → CSubst n m → RSubst
    projSubst nil = []
    projSubst (snoc s t prf x) = (toℕ x , cast t prf) ∷ projSubst s

  sortSubst : RSubst → RSubst
  sortSubst [] = []
  sortSubst ((i , t) ∷ s) = insert (i , t) (sortSubst s)
    where
      insert : (ℕ × RTerm ⊥) → RSubst → RSubst
      insert (i , t) [] = (i , t) ∷ []
      insert (i , t) (x ∷ xs) with total i (p1 x)
      ...| i1 i≤x = x ∷ insert (i , t) xs -- (i , t) ∷ x ∷ xs
      ...| i2 i>x = (i , t) ∷ x ∷ xs -- x ∷ insert (i , t) xs

  private
    overlaps : (ℕ × RTerm ⊥) → RSubst → Maybe RSubst
    overlaps r [] = just (r ∷ [])
    overlaps (i , ti) ((j , tj) ∷ s)
      with i ≟-ℕ j | ti ≟-RTerm tj
    ...| yes _ | yes _ = just []
    ...| yes _ | no  _ = nothing
    ...| no  _ | _     = overlaps (i , ti) s

  _++ᵣ_ : RSubst → RSubst → Maybe RSubst
  [] ++ᵣ s       = just s
  (r ∷ rs) ++ᵣ s with overlaps r s
  ...| nothing = nothing
  ...| just l  = (_++-List_ l) <$> (rs ++ᵣ s)

  -- Unilateral unification.
  --
  --  Since t₂ is of type (RTerm ⊥), we are pretty sure it does not
  --  have any 'ovar' inside, therefore is t₁ that drives unification.
  unify : (t₁ : RTerm ℕ)(t₂ : RTerm ⊥) → Maybe RSubst
  unify t₁ t₂ with R2FinTerm t₁ | ⊥2FinTerm t₂
  ...| (_ , f₁) | f₂ = (sortSubst ∘ projSubst ∘ p2) 
                     <$> unifyFin0 f₁ f₂
