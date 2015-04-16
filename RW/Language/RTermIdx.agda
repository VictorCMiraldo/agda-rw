open import Prelude
open import RW.Language.RTerm
open import RW.Language.FinTerm

module RW.Language.RTermIdx where

  open Eq {{...}}

  data RTermᵢ {a}(A : Set a) : Set a where
    ovarᵢ : (x : A) → RTermᵢ A
    ivarᵢ : (n : ℕ) → RTermᵢ A
    rlitᵢ : (l : Literal) → RTermᵢ A
    rlamᵢ : RTermᵢ A
    rappᵢ : (n : RTermName) → RTermᵢ A

  ovarᵢ-inj : ∀{a}{A : Set a}{x y : A} → ovarᵢ x ≡ ovarᵢ y → x ≡ y
  ovarᵢ-inj refl = refl

  ivarᵢ-inj : ∀{a}{A : Set a}{x y : ℕ} → ivarᵢ {a} {A} x ≡ ivarᵢ {a} y → x ≡ y
  ivarᵢ-inj refl = refl

  rlitᵢ-inj : ∀{a}{A : Set a}{x y : Literal} → rlitᵢ {a} {A} x ≡ rlitᵢ {a} y → x ≡ y
  rlitᵢ-inj refl = refl

  rappᵢ-inj : ∀{a}{A : Set a}{x y : RTermName} → rappᵢ {a} {A} x ≡ rappᵢ {a} y → x ≡ y
  rappᵢ-inj refl = refl

  _≟-RTermᵢ_ : {A : Set}{{eqA : Eq A}}
               → (t₁ t₂ : RTermᵢ A) → Dec (t₁ ≡ t₂)
  _≟-RTermᵢ_ {{eq _≟_}} (ovarᵢ x) (ovarᵢ y)
    with x ≟ y
  ...| yes x≡y = yes (cong ovarᵢ x≡y)
  ...| no  x≢y = no (x≢y ∘ ovarᵢ-inj)
  _≟-RTermᵢ_ (ovarᵢ _) (ivarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (ovarᵢ _) (rlitᵢ _) = no (λ ())
  _≟-RTermᵢ_ (ovarᵢ _) (rlamᵢ  ) = no (λ ())
  _≟-RTermᵢ_ (ovarᵢ _) (rappᵢ _) = no (λ ())
  _≟-RTermᵢ_ (ivarᵢ _) (ovarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (ivarᵢ x) (ivarᵢ y) 
    with x ≟-ℕ y
  ...| yes x≡y = yes (cong ivarᵢ x≡y)
  ...| no  x≢y = no (x≢y ∘ ivarᵢ-inj)
  _≟-RTermᵢ_ (ivarᵢ _) (rlitᵢ _) = no (λ ())
  _≟-RTermᵢ_ (ivarᵢ _) (rlamᵢ  ) = no (λ ())
  _≟-RTermᵢ_ (ivarᵢ _) (rappᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlitᵢ _) (ivarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlitᵢ _) (ovarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlitᵢ x) (rlitᵢ y) 
    with x ≟-Lit y
  ...| yes x≡y = yes (cong rlitᵢ x≡y)
  ...| no  x≢y = no (x≢y ∘ rlitᵢ-inj)
  _≟-RTermᵢ_ (rlitᵢ _) (rlamᵢ  ) = no (λ ())
  _≟-RTermᵢ_ (rlitᵢ _) (rappᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlamᵢ  ) (ovarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlamᵢ  ) (ivarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlamᵢ  ) (rlitᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rlamᵢ  ) (rlamᵢ  ) = yes refl
  _≟-RTermᵢ_ (rlamᵢ  ) (rappᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rappᵢ _) (ovarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rappᵢ _) (ivarᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rappᵢ _) (rlitᵢ _) = no (λ ())
  _≟-RTermᵢ_ (rappᵢ _) (rlamᵢ  ) = no (λ ())
  _≟-RTermᵢ_ (rappᵢ x) (rappᵢ y) 
    with x ≟-RTermName y 
  ...| yes x≡y = yes (cong rappᵢ x≡y)
  ...| no  x≢y = no (x≢y ∘ rappᵢ-inj)

  -----------------------------------
  -- Utilities

  out : ∀{a}{A : Set a} → RTerm A → RTermᵢ A × List (RTerm A)
  out (ovar x)    = ovarᵢ x , []
  out (ivar n)    = ivarᵢ n , []
  out (rlit l)    = rlitᵢ l , []
  out (rlam t)    = rlamᵢ , t ∷ []
  out (rapp n ts) = rappᵢ n , ts

  toSymbol : ∀{a}{A : Set a} → RTermᵢ A → Maybe A
  toSymbol (ovarᵢ a) = just a
  toSymbol _         = nothing

  idx-cast : ∀{a b}{A : Set a}{B : Set b} 
           → (i : RTermᵢ A) → (toSymbol i ≡ nothing)
           → RTermᵢ B
  idx-cast (ovarᵢ x) ()
  idx-cast (ivarᵢ n) _ = ivarᵢ n
  idx-cast (rlitᵢ l) _ = rlitᵢ l
  idx-cast (rlamᵢ  ) _ = rlamᵢ
  idx-cast (rappᵢ n) _ = rappᵢ n

  instance
    eq-RTermᵢ : {A : Set}{{eqA : Eq A}} → Eq (RTermᵢ A)
    eq-RTermᵢ = eq _≟-RTermᵢ_

  {-
  instance
  
    RTerm-isTrie : {A : Set}{{eqA : Eq A}}{{enA : Enum A}} 
                 → IsTrie (RTerm A)
    RTerm-isTrie {A} {{enA = enum aℕ ℕa}} = record
      { Idx     = RTermᵢ A
      ; idx≡    = eq _≟-RTermᵢ_
      ; toSym   = toSymAux
      ; fromSym = fromSymAux
      ; inₜ     = inAux
      ; outₜ    = outAux
      }
      where
        postulate
          fixme : ∀{a}{A : Set a} → A

        toSymAux : RTermᵢ A → Maybe ℕ
        toSymAux (ovarᵢ n) = aℕ n
        toSymAux _         = nothing

        fromSymAux : ℕ → Maybe (RTermᵢ A)
        fromSymAux n = maybe (λ x → just (ovarᵢ x)) nothing (ℕa n)

        inAux : RTermᵢ A × List (RTerm A) → RTerm A
        inAux (ovarᵢ x , []) = ovar x
        inAux (ivarᵢ x , []) = ivar x
        inAux (rlitᵢ l , []) = rlit l
        inAux (rlamᵢ , t ∷ []) = rlam t
        inAux (rappᵢ n , ts) = rapp n ts
        inAux _ = fixme -- maybe using vectors of the correct arity...

        outAux : RTerm A → RTermᵢ A × List (RTerm A)
        outAux (ovar x) = ovarᵢ x , []
        outAux (ivar n) = ivarᵢ n , []
        outAux (rlit l) = rlitᵢ l , []
        outAux (rlam t) = rlamᵢ , t ∷ []
        outAux (rapp n ts) = rappᵢ n , ts
  {-
    RTerm-isTrie : IsTrie (RTerm ⊥)
    RTerm-isTrie = record
      { Idx   = RTermᵢ ⊥
      ; idx≡  = eq _≟-RTermᵢ_
      ; toSym = toSymAux
      ; fromSym = fromSymAux
      ; inₜ   = inAux
      ; outₜ  = outAux
      } where
        postulate
          fixme : ∀{a}{A : Set a} → A

        toSymAux : RTermᵢ ⊥ → Maybe ℕ
        toSymAux (ovarᵢ ())
        toSymAux (ivarᵢ n) = just n
        toSymAux _         = nothing

        fromSymAux : ℕ → Maybe (RTermᵢ ⊥)
        fromSymAux x = just (ivarᵢ x)

        inAux : RTermᵢ ⊥ × List (RTerm ⊥) → RTerm ⊥
        inAux (ovarᵢ () , [])
        inAux (ivarᵢ x , []) = ivar x
        inAux (rlitᵢ l , []) = rlit l
        inAux (rlamᵢ , t ∷ []) = rlam t
        inAux (rappᵢ n , ts) = rapp n ts
        inAux _ = fixme -- maybe using vectors of the correct arity...

        outAux : RTerm ⊥ → RTermᵢ ⊥ × List (RTerm ⊥)
        outAux (ovar ()) -- = ovarᵢ x , []
        outAux (ivar n) = ivarᵢ n , []
        outAux (rlit l) = rlitᵢ l , []
        outAux (rlam t) = rlamᵢ , t ∷ []
        outAux (rapp n ts) = rappᵢ n , ts
  -}

  RTermTrie : (A : Set){{eqA : Eq A}}{{enA : Enum A}} → Set
  RTermTrie A = BTrie (RTerm A) Name

  insertTerm : {A : Set}{{eqA : Eq A}}{{enA : Enum A}} 
             → Name → RTerm A → ℕ × RTermTrie A → ℕ × RTermTrie A
  insertTerm {A} = insert
    where
      open import RW.Data.BTrie.Insert (RTerm A) Name

  lookupTerm : {A : Set}{{eqA : Eq A}}{{enA : Enum A}}
             → RTerm ⊥ → RTermTrie A → List (ℕmap.to (RTerm A) × Name)
  lookupTerm {A} t = lookup (replace-A ⊥-elim t)
    where
      open import RW.Data.BTrie.Lookup (RTerm A) Name

  -}
