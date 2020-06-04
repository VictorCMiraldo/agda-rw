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
    using (⊤; tt)
    public

  Unit : Set
  Unit = ⊤

  unit : Unit
  unit = tt

  open import Data.Empty
    using (⊥; ⊥-elim)
    public

  open import Function 
    using (_∘_; _$_; flip; id; const; _on_) 
    public

  open import Data.Nat 
    using (ℕ; suc; zero; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
    renaming (_≟_ to _≟-ℕ_; _≤?_ to _≤?-ℕ_)
    public
                                          
  open import Data.Fin 
    using (Fin; fromℕ; fromℕ<; toℕ)
    renaming (zero to fz; suc to fs)
    public

  open import Data.Fin.Properties 
    using ()
    renaming (_≟_ to _≟-Fin_) 
    public

  open import Data.List 
    using (List; _∷_; []; map; _++_; zip; filter;
           all; any; concat; foldr; reverse; length; boolFilter)

    public

  open import Data.Product
    using (∃; Σ; _×_; _,_; uncurry; curry)
    renaming (proj₁ to p1; proj₂ to p2
           ; <_,_> to split)
    public

  open import Data.Sum
    using (_⊎_; [_,_]′)
    renaming (inj₁ to i1; inj₂ to i2
           ; [_,_] to either)
    public

  open import Data.Bool
    using (Bool; true; false; if_then_else_; not)
    renaming (_∧_ to _and_; _∨_ to _or_)
    public

  open import Relation.Nullary
    using (Dec; yes; no; ¬_)
    public

  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; cong₂; subst)
    public

  open import Data.Maybe 
    using (Maybe; just; nothing)
    renaming (maybe′ to maybe; map to Maybe-map)
    public

  dec-elim : ∀{a b}{A : Set a}{B : Set b}
           → (A → B) → (¬ A → B) → Dec A → B
  dec-elim f g (yes p) = f p
  dec-elim f g (no  p) = g p

  dec2set : ∀{a}{A : Set a} → Dec A → Set
  dec2set (yes _) = ⊤
  dec2set (no  _) = ⊥

  isTrue : ∀{a}{A : Set a} → Dec A → Bool
  isTrue (yes _) = true
  isTrue _       = false

  takeWhile : ∀{a}{A : Set a} → (A → Bool) → List A → List A
  takeWhile _ [] = []
  takeWhile f (x ∷ xs) with f x
  ...| true = x ∷ takeWhile f xs
  ...| _    = takeWhile f xs


  -- Some minor boilerplate to solve equality problem...
  record Eq (A : Set) : Set where
    constructor eq
    field cmp : (x y : A) → Dec (x ≡ y)

  open Eq {{...}}

  record Enum (A : Set) : Set where
    constructor enum
    field
      toEnum   : A → Maybe ℕ
      fromEnum : ℕ → Maybe A

  open Enum {{...}}

  instance
    eq-ℕ : Eq ℕ
    eq-ℕ = eq _≟-ℕ_

    enum-ℕ : Enum ℕ
    enum-ℕ = enum just just

    eq-Fin : ∀{n} → Eq (Fin n)
    eq-Fin = eq _≟-Fin_

    enum-Fin : ∀{n} → Enum (Fin n)
    enum-Fin {n} = enum (λ x → just (toℕ x)) fromℕ-partial
      where
        fromℕ-partial : ℕ → Maybe (Fin n)
        fromℕ-partial m with suc m ≤?-ℕ n
        ...| yes prf = just (fromℕ< {m} {n} prf)
        ...| no  _   = nothing

    eq-⊥ : Eq ⊥
    eq-⊥ = eq (λ x → ⊥-elim x)

    enum-⊥ : Enum ⊥
    enum-⊥ = enum ⊥-elim (const nothing)

    eq-Maybe : ∀{A} ⦃ eqA : Eq A ⦄ → Eq (Maybe A)
    eq-Maybe = eq decide
      where 
        just-inj : ∀{a}{A : Set a}{x y : A}
                 → _≡_ {a} {Maybe A} (just x) (just y) → x ≡ y
        just-inj refl = refl
  
        decide : {A : Set} ⦃ eqA : Eq A ⦄
               → (x y : Maybe A) → Dec (x ≡ y)
        decide nothing nothing   = yes refl
        decide nothing (just _)  = no (λ ())
        decide (just _) nothing  = no (λ ())
        decide ⦃ eq f ⦄ (just x) (just y) with f x y
        ...| yes x≡y = yes (cong just x≡y)
        ...| no  x≢y = no (x≢y ∘ just-inj)

    enum-Maybe : ∀{A} ⦃ enA : Enum A ⦄ → Enum (Maybe A)
    enum-Maybe ⦃ enum aℕ ℕa ⦄ = enum (maybe aℕ nothing) (just ∘ ℕa)

    eq-List : {A : Set}{{eq : Eq A}} → Eq (List A)
    eq-List {A} {{eq _≟_}} = eq decide
      where
        open import Data.List.Properties
          renaming (∷-injective to ∷-inj)

        decide : (a b : List A) → Dec (a ≡ b)
        decide [] (_ ∷ _) = no (λ ())
        decide (_ ∷ _) [] = no (λ ())
        decide []   []    = yes refl
        decide (a ∷ as) (b ∷ bs)
          with a ≟ b | decide as bs
        ...| yes a≡b | yes as≡bs 
          rewrite a≡b = yes (cong (_∷_ b) as≡bs)
        ...| no  a≢b | yes as≡bs = no (a≢b ∘ p1 ∘ ∷-inj)
        ...| yes a≡b | no  as≢bs = no (as≢bs ∘ p2 ∘ ∷-inj)
        ...| no  a≢b | no  as≢bs = no (a≢b ∘ p1 ∘ ∷-inj)
