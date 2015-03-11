open import Prelude renaming (_++_ to _++-List_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_; _≤_; z≤n; s≤s; _≤?_) renaming (decTotalOrder to decTotalOrder-ℕ)
open import Data.Nat.Properties as ℕ-Props
open import Data.Nat.Properties.Simple using (+-suc; +-comm)
open import Data.Fin using (Fin; toℕ; fromℕ≤) renaming (inject+ to finject; raise to fraise; zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; sym)
open import Algebra using (module CommutativeSemiring; module DistributiveLattice)
open import Relation.Binary using (module DecTotalOrder)

open import RW.Language.RTerm
open import RW.Language.RTermUtils using (typeArity; typeResult)

-- Utility Module to handle (RTerm (Fin n)), or,
-- finite-scope terms.
--
-- Adapted from "Auto In Agda", by Pepijn Kokke and Wouter Swierstra.
--  https://github.com/pepijnkokke/AutoInAgda
--
module RW.Language.FinTerm where

  -----------------------------------------
  -- Unification/Instantiation
  --   by Structural Recursion
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

  open DistributiveLattice ℕ-Props.distributiveLattice 
    using (_∧_; ∧-comm) public
  open DecTotalOrder decTotalOrder-ℕ 
    using (total) public

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

  R2FinType : RTerm ℕ → ∃ FinTerm
  R2FinType t with typeArity t
  ...| ar = ar , replace-A fix-ovars t
    where
      fix-ovars : ℕ → FinTerm ar
      fix-ovars fn with suc fn ≤? ar
      ...| yes prf = ovar (fromℕ≤ prf)
      ...| no  _   = ivar fn
