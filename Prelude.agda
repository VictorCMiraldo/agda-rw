-- A Simple selection of modules with some renamings to
-- make my (your) life easier when starting a new agda module.
--
-- This includes standard functionality to work on:
--  1. Functions,
--  2. Naturals,
--  3. Products and Coproducts (projections and injections are p1, p2, i1, i2).
--  4. Finite Types (zero and suc are fz and fs)
--  5. Lists
--  6. Booleans and PropositionalEquality
--  7. Decidable Predicates
--
module Prelude where

  open import Data.Unit
    using (Unit; unit)
    public

  open import Function 
    using (_∘_; _$_; flip; id; const; _on_) 
    public

  open import Data.Nat 
    using (ℕ; suc; zero; _+_; _*_)
    renaming (_≟_ to _≟-ℕ_) 
    public
                                          
  open import Data.Fin 
    using (Fin; fromℕ; toℕ)
    renaming (zero to fz; suc to fs)
    public

  open import Data.Fin.Properties 
    renaming (_≟_ to _≟-Fin_) 
    public

  open import Data.List 
    using (List; _∷_; []; map; _++_; zip; filter;
           all; any; concat)
    public

  open import Data.Product
    using (∃; Σ; _×_; _,_; uncurry; curry)
    renaming (proj₁ to p1; proj₂ to p2
           ; <_,_> to split)
    public

  open import Data.Sum
    using (_⊎_)
    renaming (inj₁ to i1; inj₂ to i2
           ; [_,_] to either)
    public

  open import Data.Bool
    using (Bool; true; false; if_then_else_; not)
    renaming (_∧_ to _and_; _∨_ to _or_)
    public

  open import Relation.Nullary
    using (Dec; yes; no)
    public

  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; cong₂; subst)
    public

  isTrue : ∀{a}{A : Set a} → Dec A → Bool
  isTrue (yes _) = true
  isTrue _       = false

  takeWhile : ∀{a}{A : Set a} → (A → Bool) → List A → List A
  takeWhile _ [] = []
  takeWhile f (x ∷ xs) with f x
  ...| true = x ∷ takeWhile f xs
  ...| _    = takeWhile f xs
