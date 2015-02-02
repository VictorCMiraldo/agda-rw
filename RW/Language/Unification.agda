open import Prelude renaming (_++_ to _++-List_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_; _≤_; z≤n; s≤s) renaming (decTotalOrder to decTotalOrder-ℕ)
open import Data.Nat.Properties as ℕ-Props
open import Data.Nat.Properties.Simple using (+-suc; +-comm)
open import Data.Fin using (Fin; toℕ) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; sym)
open import Algebra using (module CommutativeSemiring; module DistributiveLattice)
open import Relation.Binary using (module DecTotalOrder)


open import Language.RTerm

-- This module is merely an adaptation of Unification.agda from
-- Auto In Agda, by Pepijn Kokke and Wouter Swierstra.
-- 
-- https://github.com/pepijnkokke/AutoInAgda
--
-- We use a different term representation; I chose to use a slightly more
-- general terms. The adaptation consists of transforming a
-- (RTerm ℕ) to a (RTerm (Fin n)), for a given n ∈ ℕ.
--
--
module Language.Unification where

  -----------------------------------------
  -- Unification by Structural Recursion
  --
  --  We have to bypass some problems with the termination checker;
  --  The trick is to represent variables using a finite datatype,
  --  this way we can prove that the index of the variables to be
  --  replaced decreases.
  --
  --  To work with FinTerms, as we'll call them:
  FinTerm : ℕ → Set
  FinTerm = RTerm ∘ Fin

  --  We're going to need a lot of machinery to inject and raise
  --  FinTerms in loads of different contexts.
  --
  --  The beginning of this module is reserved for that boilerplate.
  --
  --------------------------------------------
  -- Fin Boilerplate

  record Inject (T : ℕ → Set) : Set where
    constructor inj
    field
      inject : ∀ {m} n → T m → T (m + n)

    inject≤ : ∀ {m n} → m ≤ n → T m → T n
    inject≤ {m} {n} p t = P.subst T (sym (Δ-correct p)) (inject (Δ p) t)

  open Inject {{...}} using (inject; inject≤)

  record Raise (T : ℕ → Set) : Set where
    constructor rai
    field
      raise : ∀ {m} n → T m → T (n + m)

    raise≤ : ∀ {m n} → m ≤ n → T m → T n
    raise≤ {m} {n} p t = P.subst T (sym (P.trans (Δ-correct p) (+-comm m (Δ p)))) (raise (Δ p) t)

  open Raise {{...}} using (raise; raise≤)

  instance
    InjectFin : Inject Fin
    InjectFin = inj finject

    RaiseFin : Raise Fin
    RaiseFin = rai fraise

    InjectRTerm : Inject FinTerm
    InjectRTerm = inj (λ n → replace-A (ovar ∘ inject n))

    RaiseRTerm : Raise FinTerm
    RaiseRTerm = rai (λ n → replace-A (ovar ∘ raise n))

    InjectRTerms : Inject (List ∘ FinTerm)
    InjectRTerms = inj (λ n → map (inject n))

    RaiseRTerms : Raise (List ∘ FinTerm)
    RaiseRTerms = rai (λ n → map (raise n))

  open DistributiveLattice ℕ-Props.distributiveLattice using (_∧_; ∧-comm)
  open DecTotalOrder decTotalOrder-ℕ using (total)

  private
    supremumLemma : ∀{m n} → m ≤ n → m ∧ n ≡ n
    supremumLemma z≤n     = refl
    supremumLemma (s≤s p) = cong suc (supremumLemma p)

  -- Match indexes of injectable types.
  match : ∀{m n} {I J} ⦃ i : Inject I ⦄ ⦃ j : Inject J ⦄
        → I m → J n → I (m ∧ n) × J (m ∧ n)
  match {m} {n} i j with total m n
  ...| i1 m≤n rewrite supremumLemma m≤n = inject≤ m≤n i , j
  ...| i2 n≤m rewrite ∧-comm m n
                      | supremumLemma n≤m = i , inject≤ n≤m j

  -- Conversion of regular terms to finite terms.

  mutual
    R2FinTerm : RTerm ℕ → ∃ FinTerm
    R2FinTerm (ovar x) = suc x , ovar (fromℕ x)
    R2FinTerm (ivar n) = 0 , ivar n
    R2FinTerm (rlit l) = 0 , rlit l
    R2FinTerm (rlam t) with R2FinTerm t
    ...| (n , t') = n , rlam t'
    R2FinTerm (rapp n ts) with R2FinTerm* ts
    ...| (k , l) = k , rapp n l

    R2FinTerm* : List (RTerm ℕ) → ∃ (List ∘ FinTerm)
    R2FinTerm* [] = 0 , []
    R2FinTerm* (x ∷ xs) with R2FinTerm x | R2FinTerm* xs
    ...| kx , x' | kxs , xs' with match x' xs'
    ...| rx , rxs = kx ∧ kxs , rx ∷ rxs

  Fin2RTerm : ∀{n} → FinTerm n → RTerm ℕ
  Fin2RTerm = replace-A (ovar ∘ toℕ)

  --------------------------------------------------
  -- Monadic Boilerplate

  open import Utils.Monads
  open Monad {{...}}

  _<$>_ : ∀{a b}{A : Set a}{B : Set b} 
        → (A → B) → Maybe A → Maybe B
  _ <$> nothing  = nothing
  f <$> (just x) = just (f x)

  _<*>_ : ∀{a b}{A : Set a}{B : Set b}
        → Maybe (A → B) → Maybe A → Maybe B
  just f <*> just x = just (f x)
  _      <*> _      = nothing

  --------------------------------------------------
  -- Unification Algorithm
  --

  -- thick and thin
  thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
  thin  fzero    y       = fsuc y
  thin (fsuc x)  fzero   = fzero
  thin (fsuc x) (fsuc y) = fsuc (thin x y)

  thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
  thick          fzero    fzero    = nothing
  thick          fzero    (fsuc y) = just y
  thick {zero}  (fsuc ())  _
  thick {suc n} (fsuc x)  fzero    = just fzero
  thick {suc n} (fsuc x)  (fsuc y) = fsuc <$> thick x y

  -- occurs check (check in McBride 2003)
  check : ∀{n}(x : Fin (suc n))(t : FinTerm (suc n)) → Maybe (FinTerm n)
  check _ (rlit l) = just (rlit l)
  check x (ivar y) = just (ivar y)
  check x (ovar y) = ovar <$> thick x y
  check x (rlam t) = rlam <$> check x t
  check x (rapp n ts) = rapp n <$> checkChildren x ts
    where
      checkChildren : ∀{n} (x : Fin (suc n))(ts : List (FinTerm (suc n)))
                    → Maybe (List (FinTerm n))
      checkChildren x [] = just []
      checkChildren x (t ∷ ts) 
        = check x t >>= λ t' → checkChildren x ts >>= return ∘ (_∷_ t')

  
  -- datatype for substitutions (AList in McBride, 2003)
  data Subst : ℕ → ℕ → Set where
    nil  : ∀ {n}   → Subst n n
    snoc : ∀ {m n} → (s : Subst m n) → (t : FinTerm m) → (x : Fin (suc m)) → Subst (suc m) n

  -- substitutes t for x (**for** in McBride, 2003)
  _for_ : ∀ {n} (t : FinTerm n) (x : Fin (suc n)) → Fin (suc n) → FinTerm n
  _for_ t x y with thick x y
  _for_ t x y | just y' = ovar y'
  _for_ t x y | nothing = t

  -- substitution application (**sub** in McBride, 2003)
  apply : ∀ {m n} → Subst m n → Fin m → FinTerm n
  apply nil = ovar
  apply (snoc s t x) = (apply s) ◇-A (t for x)

  -- composes two substitutions
  _++_ : ∀ {l m n} → Subst m n → Subst l m → Subst l n
  s₁ ++ nil = s₁
  s₁ ++ (snoc s₂ t x) = snoc (s₁ ++ s₂) t x

  flexRigid : ∀ {n} → Fin n → FinTerm n → Maybe (∃ (Subst n))
  flexRigid {zero} () t
  flexRigid {suc n} x t with check x t
  flexRigid {suc n} x t | nothing = nothing
  flexRigid {suc n} x t | just t' = just (n , snoc nil t' x)

  flexFlex : ∀ {n} → (x y : Fin n) → ∃ (Subst n)
  flexFlex {zero} () j
  flexFlex {suc n} x y with thick x y
  flexFlex {suc n} x y | nothing = (suc n , nil)
  flexFlex {suc n} x y | just  z = (n , snoc nil (ovar z) x)

  mutual
    unifyAcc : ∀{m} → (t₁ t₂ : FinTerm m) → ∃ (Subst m) → Maybe (∃ (Subst m))
    unifyAcc (rlit l₁) (rlit l₂) (n , nil) with l₁ ≟-Lit l₂
    ...| yes l₁≡l₂ rewrite l₁≡l₂ = just (n , nil)
    ...| no  _     = nothing
    unifyAcc (rapp _ _) (rlit _)   _ = nothing
    unifyAcc (rapp _ _) (ivar _)   _ = nothing
    unifyAcc (rapp _ _) (rlam _)   _ = nothing
    unifyAcc (rlit _)   (ivar _)   _ = nothing
    unifyAcc (rlit _)   (rlam _)   _ = nothing
    unifyAcc (rlit _)   (rapp _ _) _ = nothing
    unifyAcc (rlam _)   (rapp _ _) _ = nothing
    unifyAcc (rlam _)   (ivar _)   _ = nothing
    unifyAcc (rlam _)   (rlit _)   _ = nothing
    unifyAcc (ivar _)   (rlit _)   _ = nothing
    unifyAcc (ivar _)   (rapp _ _) _ = nothing
    unifyAcc (ivar _)   (rlam _)   _ = nothing
    unifyAcc (ivar x)   (ivar y) acc with x ≟-ℕ y
    ...| yes x≡y = just acc
    ...| no  _   = nothing
    unifyAcc (rlam x)   (rlam y) acc = unifyAcc x y acc
    unifyAcc (rapp x ax) (rapp y ay) acc with x ≟-RTermName y
    ...| yes x≡y rewrite x≡y = unifyAccChildren ax ay acc
    ...| no  _   = nothing
    unifyAcc (ovar x)  (ovar y) (n , nil)
      = just (flexFlex x y)
    unifyAcc (ovar x)   t  (n , nil) = flexRigid x t
    unifyAcc t    (ovar x) (n , nil) = flexRigid x t
    unifyAcc t₁ t₂ (n , snoc s t′ x) =
      ( λ s → p1 s , snoc (p2 s) t′ x )
        <$> unifyAcc (replace-A (t′ for x) t₁) (replace-A (t′ for x) t₂) (n , s)

    unifyAccChildren : ∀ {n} → (ts₁ ts₂ : List (FinTerm n)) 
                     → ∃ (Subst n) → Maybe (∃ (Subst n))
    unifyAccChildren []         []       acc = just acc
    unifyAccChildren []         _        _   = nothing
    unifyAccChildren _          []       _   = nothing
    unifyAccChildren (t₁ ∷ ts₁) (t₂ ∷ ts₂) acc = unifyAcc t₁ t₂ acc >>= unifyAccChildren ts₁ ts₂

  unifyFin : ∀ {m} → (t₁ t₂ : FinTerm m) → Maybe (∃ (Subst m))
  unifyFin {m} t₁ t₂ = unifyAcc t₁ t₂ (m , nil)

  --------------------------------------------------------
  -- Interface to RTerm ℕ
  
  RSubst : Set
  RSubst = List (ℕ × RTerm ℕ)

  private
    projSubst : ∀{n m} → Subst n m → RSubst
    projSubst nil = []
    projSubst (snoc s t x) = (toℕ x , Fin2RTerm t) ∷ projSubst s

  sortSubst : RSubst → RSubst
  sortSubst [] = []
  sortSubst ((i , t) ∷ s) = insert (i , t) (sortSubst s)
    where
      insert : (ℕ × RTerm ℕ) → RSubst → RSubst
      insert (i , t) [] = (i , t) ∷ []
      insert (i , t) (x ∷ xs) with total i (p1 x)
      ...| i1 i≤x = x ∷ insert (i , t) xs -- (i , t) ∷ x ∷ xs
      ...| i2 i>x = (i , t) ∷ x ∷ xs -- x ∷ insert (i , t) xs

  private
    overlaps : (ℕ × RTerm ℕ) → RSubst → Maybe RSubst
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

  unify : (t₁ t₂ : RTerm ℕ) → Maybe RSubst
  unify t₁ t₂ with R2FinTerm t₁ | R2FinTerm t₂
  ...| (_ , f₁) | (_ , f₂) with match f₁ f₂
  ...| r₁ , r₂ = (sortSubst ∘ projSubst ∘ p2) <$> unifyFin r₁ r₂
