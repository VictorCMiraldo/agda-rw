open import Level using (_⊔_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Any as A hiding (map)
open import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary

open import Prelude hiding (map)
open Eq {{...}}

module RW.Data.PMap (A : Set){{eqA : Eq A}} where

  private
    _≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)
    a₁ ≟ a₂ = Eq.cmp eqA a₁ a₂

  -- Naive Partial Map representation
  to_ : ∀{b} → Set b → Set b
  to B = List (A × B)

  empty : ∀{b}{B : Set b}
        → to B
  empty = []

  -- Membership
  _∈_ : ∀{b}{B : Set b}
      → A → (to B) → Set _
  a ∈ m = A.Any ((_≡_ a) ∘ p1) m

  _∉_ : ∀{b}{B : Set b}
      → A → (to B) → Set _
  a ∉ m = (a ∈ m) → ⊥

  -- Decidable membership
  dec∈ : ∀{b}{B : Set b}
       → (a : A) → (m : to B) → Dec (a ∈ m)
  dec∈ a [] = no (λ ())
  dec∈ a (x ∷ m) with a ≟ (p1 x)
  ...| yes a≡x = yes (here a≡x)
  ...| no  a≢x with dec∈ a m
  ...| yes a∈m = yes (there a∈m)
  ...| no  a∉m = no (a∉m ∘ tail a≢x)
  

  -- Look up
  lkup : ∀{b}{B : Set b} → A → (to B) → Maybe B
  lkup k [] = nothing
  lkup k ((h , r) ∷ ts) 
    with k ≟ h
  ...| yes _ = just r
  ...| no  _ = lkup k ts

  -- Total version
  lkup' : ∀{b}{B : Set b}
        → (a : A) → (m : to B) → a ∈ m → B
  lkup' a (m ∷ _)  (here px)   = p2 m
  lkup' a (_ ∷ ms) (there prf) = lkup' a ms prf

  -- Insertion / Removal
  alter : ∀{b}{B : Set b}
        → (Maybe B → Maybe B) → A → (to B) → (to B)
  alter f a [] with f nothing
  ...| just b  = (a , b) ∷ []
  ...| nothing = []
  alter f a (x ∷ m) with a ≟ p1 x
  ...| no  _ = x ∷ alter f a m
  ...| yes _ with f $ just (p2 x)
  ...| nothing = m
  ...| just b  = (a , b) ∷ m

  alterPrf : ∀{b}{B : Set b}
           → B → (a : A) → (m : to B) → Σ (to B) (_∈_ a)
  alterPrf b a m with dec∈ a m
  ...| yes a∈m = m , a∈m
  ...| no  a∉m = (a , b) ∷ m , here refl

  insert : ∀{b}{B : Set b}
         → A → B → (to B) → (to B)
  insert a b m = alter (const $ just b) a m

  delete : ∀{b}{B : Set b}
         → A → (to B) → (to B)
  delete a m = alter (const nothing) a m

  -- Map
  map : ∀{b}{B B′ : Set b} → (B → B′) → (to B) → (to B′)
  map f [] = []
  map f ((a , b) ∷ m) = (a , f b) ∷ map f m
