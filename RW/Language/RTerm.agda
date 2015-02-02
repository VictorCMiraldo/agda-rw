open import Prelude
open import Level using (Level) renaming (zero to lz; suc to ls)
open import Data.List.Properties as ListProps renaming (∷-injective to ∷-inj)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String
open import Data.Nat as Nat using (decTotalOrder; _≤_; s≤s; z≤n)
open import Relation.Binary using (module DecTotalOrder)

module Language.RTerm where
  
  open import Reflection renaming (Term to AgTerm; Type to AgType)
    public

  open DecTotalOrder Nat.decTotalOrder using (total)

  postulate
    unsuportedSyntax : ∀{a}{A : Set a} → String → A
    error            : ∀{a}{A : Set a} → String → A
  
  -- Some minor boilerplate to solve equality problem...
  record Eq (A : Set) : Set where
    constructor eq
    field cmp : (x y : A) → Dec (x ≡ y)

  open Eq {{...}}

  instance
    eq-ℕ : Eq ℕ
    eq-ℕ = eq _≟-ℕ_

    eq-Fin : ∀{n} → Eq (Fin n)
    eq-Fin = eq _≟-Fin_

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

  -- We'll consider constructor and definitions
  -- as just names; we just need to know how to 
  -- translate them back into a correct AgTerm.
  --
  -- Function type is represented with the impl constructor.
  data RTermName : Set where
    rcon : Name → RTermName
    rdef : Name → RTermName
    impl : RTermName
  
  ----------------------------------------
  -- Equalities associated with RTermNames

  rcon-inj : ∀{x y} → rcon x ≡ rcon y → x ≡ y
  rcon-inj refl = refl

  rdef-inj : ∀{x y} → rdef x ≡ rdef y → x ≡ y
  rdef-inj refl = refl  

  _≟-RTermName_ : (n m : RTermName) → Dec (n ≡ m)
  rcon x ≟-RTermName rcon y with x ≟-Name y
  ...| yes x≡y = yes (cong rcon x≡y)
  ...| no  x≢y = no (x≢y ∘ rcon-inj)
  rdef x ≟-RTermName rdef y with x ≟-Name y
  ...| yes x≡y = yes (cong rdef x≡y)
  ...| no  x≢y = no (x≢y ∘ rdef-inj)
  impl ≟-RTermName impl     = yes refl
  rcon _ ≟-RTermName rdef _ = no (λ ())
  rcon _ ≟-RTermName impl   = no (λ ())
  rdef _ ≟-RTermName rcon _ = no (λ ())
  rdef _ ≟-RTermName impl   = no (λ ())
  impl ≟-RTermName rcon _   = no (λ ())
  impl ≟-RTermName rdef _   = no (λ ())
    
  -- Now we'll define a very handy term representation.
  -- We aim to reduce the amount of boilerplate code
  -- needed to handle Agda's complex term representation.
  --
  -- The phantom A will allow us to use multiple representations
  -- for unification variables and still prove termination
  -- by using a (Fin n), before unifying.
  data RTerm {a}(A : Set a) : Set a where
    -- Out-of-bound variables. We use a phantom type A
    -- to be able to (almost) seamless convert from
    -- ℕ to (Fin n).
    ovar : (x : A) → RTerm A

    -- Variables bound inside the term itself, from
    -- rlam's.
    ivar : (n : ℕ) → RTerm A

    -- Agda Literals
    rlit : (l : Literal) → RTerm A
    
    -- Lambda Abstraction
    rlam : RTerm A → RTerm A

    -- Applications
    rapp : (n : RTermName)(ts : List (RTerm A)) → RTerm A

  -- Equality Rules induced by RTerm's constructors

  ovar-inj : ∀{a}{A : Set a}{x y : A} → ovar {a} {A} x ≡ ovar {a} {A} y → x ≡ y
  ovar-inj refl = refl

  ivar-inj : ∀{a A x y} → ivar {a} {A} x ≡ ivar {a} {A} y → x ≡ y
  ivar-inj refl = refl

  rlit-inj : ∀{a A x y} → rlit {a} {A} x ≡ rlit {a} {A} y → x ≡ y
  rlit-inj refl = refl

  rlam-inj : ∀{a A x y} → rlam {a} {A} x ≡ rlam {a} {A} y → x ≡ y
  rlam-inj refl = refl

  rapp-inj : ∀{a A n₁ n₂ l₁ l₂}
           → rapp {a} {A} n₁ l₁ ≡ rapp {a} {A} n₂ l₂
           → n₁ ≡ n₂ × l₁ ≡ l₂
  rapp-inj refl = refl , refl

  --------------------------
  -- Generalized Comparison

  mutual
    compRTerm : ∀{A} ⦃ eqA : Eq A ⦄
              → (m n : RTerm A)
              → Dec (m ≡ n)
    compRTerm ⦃ eq f ⦄ (ovar x) (ovar y) with f x y
    ...| yes x≡y = yes (cong ovar x≡y)
    ...| no  x≢y = no (x≢y ∘ ovar-inj)
    compRTerm (ivar x) (ivar y) with x ≟-ℕ y
    ...| yes x≡y = yes (cong ivar x≡y)
    ...| no  x≢y = no (x≢y ∘ ivar-inj)
    compRTerm (rlit x) (rlit y) with x ≟-Lit y
    ...| yes x≡y = yes (cong rlit x≡y)
    ...| no  x≢y = no (x≢y ∘ rlit-inj)
    compRTerm (rlam x) (rlam y) with compRTerm x y
    ...| yes x≡y = yes (cong rlam x≡y)
    ...| no  x≢y = no (x≢y ∘ rlam-inj)
    compRTerm (rapp x ax) (rapp y ay) with x ≟-RTermName y
    ...| no  x≢y = no (x≢y ∘ p1 ∘ rapp-inj)
    ...| yes x≡y rewrite x≡y with compRTerm* ax ay
    ...| no  ax≢ay = no (ax≢ay ∘ p2 ∘ rapp-inj)
    ...| yes ax≡ay = yes (cong (rapp y) ax≡ay)
    compRTerm (ovar _) (ivar _)   = no (λ ())
    compRTerm (ovar _) (rlit _)   = no (λ ())
    compRTerm (ovar _) (rlam _)   = no (λ ())
    compRTerm (ovar _) (rapp _ _) = no (λ ())
    compRTerm (ivar _) (ovar _)   = no (λ ())
    compRTerm (ivar _) (rlit _)   = no (λ ())
    compRTerm (ivar _) (rlam _)   = no (λ ())
    compRTerm (ivar _) (rapp _ _) = no (λ ())
    compRTerm (rlit _) (ovar _)   = no (λ ())
    compRTerm (rlit _) (ivar _)   = no (λ ())
    compRTerm (rlit _) (rlam _)   = no (λ ())
    compRTerm (rlit _) (rapp _ _) = no (λ ())
    compRTerm (rlam _) (ovar _)   = no (λ ())
    compRTerm (rlam _) (ivar _)   = no (λ ())
    compRTerm (rlam _) (rlit _)   = no (λ ())
    compRTerm (rlam _) (rapp _ _) = no (λ ())
    compRTerm (rapp _ _) (ovar _) = no (λ ())
    compRTerm (rapp _ _) (ivar _) = no (λ ())
    compRTerm (rapp _ _) (rlit _) = no (λ ())
    compRTerm (rapp _ _) (rlam _) = no (λ ())

    compRTerm* : ∀{A} ⦃ eqA : Eq A ⦄
               → (x y : List (RTerm A))
               → Dec (x ≡ y)
    compRTerm* [] [] = yes refl
    compRTerm* (_ ∷ _) []  = no (λ ())
    compRTerm* [] (_ ∷ _)  = no (λ ())
    compRTerm* (x ∷ xs) (y ∷ ys) 
      with compRTerm x y
    ...| no  x≢y = no (x≢y ∘ p1 ∘ ∷-inj)
    ...| yes x≡y rewrite x≡y with compRTerm* xs ys
    ...| no  xs≢ys = no (xs≢ys ∘ p2 ∘ ∷-inj)
    ...| yes xs≡ys = yes (cong (_∷_ y) xs≡ys)

  -- Infix version

  _≟-RTerm_ : ∀{A} ⦃ eqA : Eq A ⦄ → (x y : RTerm A) → Dec (x ≡ y)
  _≟-RTerm_ = compRTerm

  ------------------------------
  -- Term Replacement Functions

  {-# TERMINATING #-}
  replace : ∀{a b}{A : Set a}{B : Set b}
          → (ovar-f : A → RTerm B)
          → (ivar-f : ℕ → RTerm B)
          → RTerm A → RTerm B
  replace f g (ovar x) = f x
  replace f g (ivar n) = g n
  replace _ _ (rlit l) = rlit l
  replace f g (rlam x) = rlam (replace f g x)
  replace f g (rapp n ts) = rapp n (map (replace f g) ts)  

  -- This is basically fmap...
  replace-A : ∀{a b}{A : Set a}{B : Set b} 
            → (A → RTerm B) → RTerm A → RTerm B
  replace-A f = replace f ivar

  _◇-A_ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
        → (B → RTerm C) → (A → RTerm B)
        → A → RTerm C
  f ◇-A g = replace-A f ∘ g

  replace-ivar : ∀{a}{A : Set a} 
               → (ℕ → RTerm A) → RTerm A → RTerm A
  replace-ivar f = replace ovar f

  ----------------------
  -- Counting utilities
  
  {-# TERMINATING #-}
  count : ∀{a}{A : Set a} → RTerm A → ℕ × ℕ
  count (ovar _) = 1 , 0
  count (ivar _) = 0 , 1
  count (rlit _) = 0 , 0
  count (rlam x) = count x
  count (rapp _ xs) = sum2 (map count xs)
    where
      sum2 : List (ℕ × ℕ) → ℕ × ℕ
      sum2 [] = 0 , 0
      sum2 ((a , b) ∷ xs) with sum2 xs
      ...| a' , b' = a + a' , b + b'

  #-A : ∀{a}{A : Set a} → RTerm A → ℕ
  #-A = p1 ∘ count

  #-ivar : ∀{a}{A : Set a} → RTerm A → ℕ
  #-ivar = p2 ∘ count

  -----------------------------------
  -- Conversion from AgTerm to RTerm

    -- compute the difference between two natural numbers, given an
  -- ordering between them.
  Δ_ : ∀ {m n} → m ≤ n → ℕ
  Δ z≤n {k} = k
  Δ s≤s  p  = Δ p

  -- correctness proof of the difference operator Δ.
  Δ-correct : ∀ {m n} (p : m ≤ n) → n ≡ m + Δ p
  Δ-correct  z≤n    = refl
  Δ-correct (s≤s p) = cong suc (Δ-correct p)

  _-Δ-_ : ∀{m}(n : ℕ)(p : m ≤ n) → ℕ 
  n       -Δ- z≤n     = n
  (suc n) -Δ- s≤s prf = n -Δ- prf

  private
    convertℕ : ℕ → RTerm ℕ
    convertℕ zero    = rapp (rcon (quote zero)) []
    convertℕ (suc n) = rapp (rcon (quote suc)) (convertℕ n ∷ [])

    mutual
      convert' : ℕ → AgTerm → RTerm ℕ
      convert' d (var x []) with total d x
      ...| i1 d≤x = ovar (Δ d≤x)
      ...| i2 d>x = ivar x
      convert' d (lit (nat n)) = convertℕ n
      convert' d (con c args)
        = rapp (rcon c) (convertChildren d args)
      convert' d (def c args)
        = rapp (rdef c) (convertChildren d args)
      convert' d (pi (arg (arg-info visible _) (el _ t₁)) (abs _ (el _ t₂)))
        = rapp impl (convert' d t₁ ∷ convert' (suc d) t₂ ∷ [])
      convert' d (pi _ (abs _ (el _ t₂))) = convert' (suc d) t₂
      convert' d (lam _ (abs _ l)) 
        = rlam (convert' (suc d) l)
      convert' d _
        = unsuportedSyntax "..."

      convertChildren : ℕ → List (Arg AgTerm) → List (RTerm ℕ)
      convertChildren d [] = []
      convertChildren d (arg (arg-info visible _) x ∷ xs)
        = convert' d x ∷ convertChildren d xs
      convertChildren d (_ ∷ xs) = convertChildren d xs

  Ag2RTerm : AgTerm → RTerm ℕ
  Ag2RTerm a = convert' 0 a

  ------------------------------------------
  -- Handling Types

  Ag2RType : AgType → RTerm ℕ
  Ag2RType (el _ t) = Ag2RTerm t

  -----------------------------------------
  -- Converting Back to Agda

  open import Utils.Monads using (MonadState; ST; get; inc) renaming (module Monad to MonadClass)
  open MonadClass {{...}}

  private
    mutual
      -- We'll keep a counter on the number of
      -- ovar's we find. We might need to add the correct number of
      -- lambdas around.
      trevnoc' : RTerm ℕ → ℕ × AgTerm
      trevnoc' (ovar x) = 1 , var x []
      trevnoc' (ivar n) = 0 , var n []
      trevnoc' (rlit l) = 0 , lit l
      trevnoc' (rlam t) with trevnoc' t
      ...| (r , t') = r , lam visible (abs "_" t')
      trevnoc' (rapp (rcon x) ts) with trevnocChildren ts
      ...| (r , a)  = r , con x a
      trevnoc' (rapp (rdef x) ts) with trevnocChildren ts
      ...| (r , a)  = r , def x a
      trevnoc' (rapp impl (t1 ∷ t2 ∷ []))
        with trevnoc' t1 | trevnoc' t2
      ...| (r1 , t1') | (r2 , t2') = r1 + r2 , pi (arg (arg-info visible relevant) (el unknown t1')) 
                                                  (abs "_" (el unknown t2'))
      trevnoc' (rapp impl _) = error "impl should have two arguments... always."

      trevnocChildren : List (RTerm ℕ) → ℕ × List (Arg AgTerm)
      trevnocChildren [] = 0 , []
      trevnocChildren (x ∷ xs) with trevnoc' x | trevnocChildren xs
      ...| (r , x') | (rs , xs') = r + rs , arg (arg-info visible relevant) x' ∷ xs'

  R2AgTerm : RTerm ℕ → AgTerm
  R2AgTerm = p2 ∘ trevnoc'
