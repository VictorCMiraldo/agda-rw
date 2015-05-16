open import Prelude
open import Data.Nat using (_≤?_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Reflection using (_≟-Lit_; _≟-Name_)

open import RW.Language.RTerm
open import RW.Utils.Monads

module RW.Language.RTermUtils where

  open Monad {{...}}

  --   The complexity annotations might require 
  --   a slight notational introduction.
  --
  --   If a variable name overlaps one in the corresponding type signature,
  --   this is intentional.
  --
  --   Sₜ is defined by (S t).
  --   #Fvₜ is defined by length (Fv t).
  --   Both measures are defined below.
  --

  --------------
  -- Measures --
  --------------

  -- The TERMINATING pragmas are required since Agda does not
  -- recognize a call to map as terminating.

  {-# TERMINATING #-}
  height : {A : Set} → RTerm A → ℕ
  height (ovar _)    = 0
  height (ivar _)    = 0
  height (rlit _)    = 0
  height (rlam t)    = 1 + height t
  height (rapp _ ts) = 1 + max* (map height ts) 
    where
      max : ℕ → ℕ → ℕ
      max a b with a ≤? b
      ...| yes _ = b
      ...| no  _ = a

      max* : List ℕ → ℕ
      max* [] = 0
      max* (h ∷ t) = max h (max* t)

  {-# TERMINATING #-}
  S : {A : Set} → RTerm A → ℕ
  S (ovar _) = 1
  S (ivar _) = 1
  S (rlit _) = 1
  S (rlam t) = 1 + S t
  S (rapp n ts) = 1 + sum (map S ts)
    where open import Data.List using (sum)

  {-# TERMINATING #-}
  Fv : {A : Set} → RTerm A → List A
  Fv (ovar a) = a ∷ []
  Fv (ivar _) = []
  Fv (rlit _) = []
  Fv (rlam t) = Fv t
  Fv (rapp _ ts) = concatMap Fv ts
    where open import Data.List using (concatMap)

  -------------------------------------------------------
  -- Terms with Context
  --
  --   Holes will be represented by a nothing;
  pattern hole = ovar nothing

  isHole : ∀{a}{A : Set a} → RTerm (Maybe A) → Bool
  isHole (ovar nothing) = true
  isHole _              = false

  -- Term Intersection
  --
  -- Complexity analisys follows below.
  {-# TERMINATING #-}
  _∩_ : ∀{A} ⦃ eqA : Eq A ⦄ 
      → RTerm A → RTerm A → RTerm (Maybe A)
  _∩_ (rapp x ax) (rapp y ay) with x ≟-RTermName y
  ...| no  _ = ovar nothing
  ...| yes _ = rapp x (map (uncurry _∩_) (zip ax ay))
  _∩_ (ivar x) (ivar y) with x ≟-ℕ y
  ...| no  _ = ovar nothing
  ...| yes _ = ivar x
  _∩_ ⦃ eq _≟_ ⦄ (ovar x) (ovar y) with x ≟ y
  ...| no  _ = ovar nothing
  ...| yes _ = ovar (just x)
  _∩_ (rlit x) (rlit y) with x ≟-Lit y
  ...| no  _ = ovar nothing
  ...| yes _ = rlit x
  _∩_ (rlam x) (rlam y) = rlam (x ∩ y)
  _∩_ _ _ = ovar nothing

  -- The wors case for a intersection is, of course, both terms being
  -- equal. But in that case, (t ∩ t) is just a (fmap just), as we
  -- can see below.
  --
  -- Therefore, _∩_ ∈ O(Sₜ)
  private
    mutual
      t∩t≡t : {A : Set}⦃ eqA : Eq A ⦄{t : RTerm A}
            → t ∩ t ≡ replace-A (ovar ∘ just) t
      t∩t≡t ⦃ eq _≟_ ⦄ {t = ovar x} with x ≟ x
      ...| yes x≡x = refl
      ...| no  x≢x = ⊥-elim (x≢x refl)
      t∩t≡t {t = ivar n} with n ≟-ℕ n
      ...| yes n≡n = refl
      ...| no  n≢n = ⊥-elim (n≢n refl)
      t∩t≡t {t = rlit l} with l ≟-Lit l
      ...| yes l≡l = refl
      ...| no  l≢l = ⊥-elim (l≢l refl)
      t∩t≡t {A} {t = rlam t} 
        = trans (cong rlam (t∩t≡t {t = t})) 
                (sym (lemma-replace-rlam {A = A} {f = ovar ∘ just} {t = t}))
      t∩t≡t {t = rapp n ts} with n ≟-RTermName n
      ...| no  n≢n = ⊥-elim (n≢n refl)
      ...| yes n≡n = cong (rapp n) t∩t≡t*

      t∩t≡t* : {A : Set}⦃ eqA : Eq A ⦄{ts : List (RTerm A)}
             → map (uncurry _∩_) (zip ts ts) 
             ≡ map (replace-A (ovar ∘ just)) ts
      t∩t≡t* {ts = []} = refl
      t∩t≡t* {ts = t ∷ ts} 
        rewrite sym (t∩t≡t {t = t}) = cong (_∷_ (t ∩ t)) (t∩t≡t* {ts = ts})

  -- Lifting holes.
  --
  --  Will translate every definition with only holes as arguments
  --  into a single hole.
  -- 
  --  The worst case for lifting holes is to find a term t
  --  with no holes. Therefore _↑ ∈ O(Sₜ).
  {-# TERMINATING #-}
  _↑ : ∀{a}{A : Set a} → RTerm (Maybe A) → RTerm (Maybe A)
  _↑ (rapp x []) = rapp x []
  _↑ (rapp x ax) with all isHole ax
  ...| true   = ovar nothing
  ...| false  = rapp x (map _↑ ax)
  _↑ (rlam x) = rlam (x ↑)
  _↑ t        = t

  -- It is commom to need only "linear" intersections;
  --
  -- _∩↑_ ∈ O(Sₜ + Sₜ) ≈ O(Sₜ)
  --
  _∩↑_ : ∀{A} ⦃ eqA : Eq A ⦄ 
       → RTerm A → RTerm A → RTerm (Maybe A)
  v ∩↑ u = (v ∩ u) ↑

  -- Casting
  ⊥2UnitCast : RTerm (Maybe ⊥) → RTerm Unit
  ⊥2UnitCast = replace-A (maybe ⊥-elim (ovar unit))

  -- Converting Holes to Abstractions
  --
  --  Will replace holes for "var 0", 
  --  and increment every other non-captured variable.
  --
  {-# TERMINATING #-}
  holeElim : ℕ → RTerm Unit → RTerm ⊥
  holeElim d (ovar unit) = ivar zero
  holeElim d (ivar n) with suc n ≤? d
  ...| yes _ = ivar n
  ...| no  _ = ivar (suc n)
  holeElim d (rlit l) = rlit l
  holeElim d (rlam rt) = rlam (holeElim (suc d) rt)
  holeElim d (rapp n ts) = rapp n (map (holeElim d) ts)

  -- Specialized version for handling indexes.
  hole2Abs : RTerm Unit → RTerm ⊥
  hole2Abs = rlam ∘ holeElim 0

  hole2Absℕ : RTerm Unit → RTerm ℕ
  hole2Absℕ = replace-A ⊥-elim ∘ hole2Abs

  open import Data.String hiding (_++_)
  postulate
    err : ∀{a}{A : Set a} → String → A

  private
    joinInner : {A : Set} → List (Maybe (List A)) → Maybe (List A)
    joinInner [] = just []
    joinInner (nothing ∷ _) = nothing -- err "2"
    joinInner (just x ∷ xs) = maybe (λ l → just (x ++ l)) nothing (joinInner xs)

    lemma-joinInner : {A : Set}{x : List A}{l : List (Maybe (List A))}
                    → joinInner (just x ∷ l) 
                    ≡ maybe (λ l → just (x ++ l)) nothing (joinInner l)
    lemma-joinInner = refl

  -- Term Subtraction
  -- 
  -- Compelxity analisys follows below.
  --
  {-# TERMINATING #-}
  _-_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (List (RTerm A))
  hole - t = return (t ∷ [])
  (rapp x ax) - (rapp y ay) with x ≟-RTermName y
  ...| no  _ = nothing -- err "1"
  ...| yes _ = joinInner (map (uncurry _-_) (zip ax ay))       
  (rlam x) - (rlam y) = x - y
  x - y with x ≟-RTerm (replace-A (ovar ∘ just) y)
  ...| yes _ = just []
  ...| no  _ = nothing -- err "3"

  -- Similarly to _∩_, we will prove the worst case complexity
  -- based on lemma t-t≡Fvt. 
  -- That is, looking at term subtraction, the wors possible case
  -- is that our roadmap (RTerm (Maybe A)) perfectly matches the
  -- term we are looking for, and has all occurences of ovars as holes.
  -- (a simple drawing might help to see this).
  --
  -- Well, when this is the case, our lemma tells us that
  -- subtraction is the same as getting the free variables
  -- and mapping ovar over them.
  --
  -- It is clear that we have some additional complexity on
  -- the function joinInner, but we will ignore this for
  -- the sake of simplicity, for now.
  -- 
  -- We'll then say that _-_ ∈ O(#Fvₜ).
  --
  private
    fmap-nothing : {A : Set} → RTerm A → RTerm (Maybe A)
    fmap-nothing = replace-A (const $ ovar nothing)

    mutual
      t-t≡Fvt : {A : Set}⦃ eqA : Eq A ⦄(t : RTerm A)
              → (fmap-nothing t) - t 
              ≡ just (map ovar (Fv t))
      t-t≡Fvt (ovar x) = refl
      t-t≡Fvt (ivar n) with n ≟-ℕ n
      ...| yes n≡n = refl
      ...| no  n≢n = ⊥-elim (n≢n refl)
      t-t≡Fvt (rlit l) with l ≟-Lit l
      ...| yes l≡l = refl
      ...| no  l≢l = ⊥-elim (l≢l refl)
      t-t≡Fvt (rlam t) = t-t≡Fvt t
      t-t≡Fvt (rapp n ts) with n ≟-RTermName n
      ...| yes n≡n = t-t≡Fvt* ts
      ...| no  n≢n = ⊥-elim (n≢n refl)

      t-t≡Fvt* : {A : Set}⦃ eqA : Eq A ⦄(ts : List (RTerm A))
               → joinInner (map (uncurry _-_) (zip (map fmap-nothing ts) ts)) 
               ≡ just (map ovar (concat (map Fv ts)))
      t-t≡Fvt* [] = refl
      t-t≡Fvt* (t ∷ ts) 
        rewrite t-t≡Fvt t
        with joinInner (map (uncurry _-_) (zip (map fmap-nothing ts) ts))
           | t-t≡Fvt* ts
      t-t≡Fvt* (t ∷ ts) | nothing | ()
      t-t≡Fvt* (t ∷ ts) | just .(map ovar (foldr _++_ [] (map Fv ts)))
                        | refl 
        = cong just (sym (map-++-commute ovar (Fv t) (concat (map Fv ts))))
        where open import Data.List.Properties using (map-++-commute)
      

  -- Term Subtraction, single result.
  _-↓_ : ∀{A} ⦃ eqA : Eq A ⦄ → RTerm (Maybe A) → RTerm A → Maybe (RTerm A)
  t -↓ u with t - u
  ...| just []      = nothing
  ...| just (x ∷ _) = just x
  ...| nothing      = nothing

  -- Structural Manipulation

  {-# TERMINATING #-}
  lift-ivar' : ℕ → RTerm ⊥ → RTerm ℕ
  lift-ivar' _ (ovar ())
  lift-ivar' d (ivar n) with d ≤? n
  ...| yes _ = ovar n
  ...| no  _ = ivar n
  lift-ivar' _ (rlit l) = rlit l
  lift-ivar' d (rlam t) = rlam (lift-ivar' (suc d) t)
  lift-ivar' d (rapp n ts) = rapp n (map (lift-ivar' d) ts)
  
  -- Lift ivar's to ovar's
  lift-ivar : RTerm ⊥ → RTerm ℕ
  lift-ivar = lift-ivar' 0
  
  -- Models a binary application
  RBinApp : ∀{a} → Set a → Set _
  RBinApp A = RTermName × RTerm A × RTerm A

  -- Opens a term representing a binary application.
  forceBinary : ∀{a}{A : Set a} 
              → RTerm A → Maybe (RBinApp A)
  forceBinary (rapp n (a₁ ∷ a₂ ∷ [])) = just (n , a₁ , a₂)
  forceBinary _                       = nothing

  -- Given a 'impl' chain, return it's result.
  typeResult : ∀{a}{A : Set a}
             → RTerm A → RTerm A
  typeResult (rapp impl (t1 ∷ t2 ∷ [])) = typeResult t2
  typeResult t = t

  -- Gives the length of a 'impl' chain.
  typeArity : ∀{a}{A : Set a} → RTerm A → ℕ
  typeArity (rapp impl (t1 ∷ t2 ∷ [])) = suc (typeArity t2)
  typeArity _                          = 0
