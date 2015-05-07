open import Prelude

open import Relation.Binary.PropositionalEquality
open import RW.Language.RTerm using (Name)
open import RW.Strategy.PropEq
open import RW.RW (≡-strat ∷ [])

open import Data.Nat.Properties.Simple 
  using (+-comm; +-right-identity; +-assoc)

module PropEqTest where

    ++-assoc : ∀{a}{A : Set a}(xs ys zs : List A) → 
               (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs       = refl
    ++-assoc (x ∷ xs) ys zs = tactic (by (quote ++-assoc))
  
    open ≡-Reasoning

    ++-assocH : ∀{a}{A : Set a}(xs ys zs : List A) →
                (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assocH [] ys zs = 
              begin 
                ([] ++ ys) ++ zs
              ≡⟨ refl ⟩
                ys ++ zs
              ≡⟨ refl ⟩
                [] ++ (ys ++ zs)
              ∎
    ++-assocH {A = A} (x ∷ xs) ys zs =
              begin
                ((x ∷ xs) ++ ys) ++ zs
              ≡⟨ refl ⟩
                x ∷ (xs ++ ys) ++ zs
              ≡⟨ refl ⟩
                x ∷ ((xs ++ ys) ++ zs)
              ≡⟨ (tactic (by (quote ++-assocH))) ⟩ 
                x ∷ (xs ++ (ys ++ zs))
              ≡⟨ refl ⟩
                (x ∷ xs) ++ (ys ++ zs)
              ∎

    []-++-neutral : ∀{a}{A : Set a}(xs : List A)
                  → xs ++ [] ≡ xs
    []-++-neutral [] = refl
    []-++-neutral (x ∷ xs) = tactic (by (quote []-++-neutral))

    test1 : (x y : ℕ) → (x + y) + 0 ≡ y + (x + 0)
    test1 x y
      = begin
        (x + y) + 0
      ≡⟨ (tactic (by+ acts)) ⟩
        x + y
      ≡⟨ (tactic (by+ acts)) ⟩
        y + x
      ≡⟨ (tactic (by+ acts)) ⟩
        (y + x) + 0
      ≡⟨ (tactic (by+ acts)) ⟩
        y + (x + 0)
      ∎
      where
        acts : List Name
        acts = quote +-right-identity ∷ quote +-assoc ∷ quote +-comm ∷ []
