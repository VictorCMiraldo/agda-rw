open import Prelude

open import Level using (_⊔_; Lift; lift) renaming (suc to ls; zero to lz)
open import Data.String using (String)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)

open import RW.Data.RTrie.Decl

module RW.Data.RTrie.Lookup
    where

  postulate 
    trie-err : ∀{a}{A : Set a} → String → A 
  
  open import RW.Utils.Monads
  open Monad {{...}}
  open Eq {{...}}

  import RW.Data.PMap (RTermᵢ ⊥) as IdxMap
  import RW.Data.PMap ℕ as ℕmap

  -------------------------------
  -- Some type boilerplate

  Label : Set
  Label = ℕ ⊎ Name

  Lst : Set
  Lst = ℕmap.to (RTerm ⊥) × Maybe Label

  Lst-empty : Lst
  Lst-empty = ℕmap.empty , nothing

  Lst-open : Lst → (ℕmap.to (RTerm ⊥) × Maybe Name)
  Lst-open (e , l) = (e , lbl-join l)
    where
      lbl-join : Maybe Label → Maybe Name
      lbl-join nothing = nothing
      lbl-join (just (i1 _)) = nothing
      lbl-join (just (i2 a)) = just a

  ---------------------------
  -- Lookup monad

  L : Set → Set
  L = Reader (List Lst)

  ----------------------------
  -- Rule application

  -- Note how a mismatch erases labels!
  applyBRule1 : Rule → Lst → Lst
  applyBRule1 (Gr x)   (e , _) = e , just (i1 x)
  applyBRule1 (Tr x y) (e , just (i1 l)) 
    with x ≟-ℕ l
  ...| yes _ = e , just (i1 y)
  ...| no  _ = e , nothing
  applyBRule1 (Tr x y) (e , just (i2 _)) = e , nothing
  applyBRule1 (Fr x y) (e , just (i1 l))
    with x ≟-ℕ l
  ...| yes _ = e , just (i2 y)
  ...| no  _ = e , nothing
  applyBRule1 (Fr _ _) (e , just (i2 _)) = e , nothing
  applyBRule1 _        (e , nothing) = e , nothing

  applyBRule : Rule → L (List Lst)
  applyBRule r = reader-ask >>= return ∘ (Prelude.map (applyBRule1 r))
  
  ruleList : List Rule → L (List Lst)
  ruleList rs = mapM applyBRule rs >>= return ∘ concat
    where
      isNothing : ∀{a}{A : Set a} → Maybe A → Bool
      isNothing nothing = true
      isNothing _       = false

      prune : List Lst → List Lst
      prune = Prelude.filter (isNothing ∘ p2)

  ------------------------------
  -- Actual Lookup

  map-filter : ∀{a}{A B : Set a} → (B → Bool) → (A → B) → List A → List B
  map-filter p f = foldr (λ h r → let x = f h in ite (p x) (x ∷ r) r) []
    where
      ite : ∀{a}{A : Set a} → Bool → A → A → A
      ite true  t _ = t
      ite false _ e = e

  mutual
    -- TODO: refine this, only apply the rules after validating and adding bindings.
    lkup-inst1 : RTerm ⊥ → ℕ × List Rule → L (List Lst)
    lkup-inst1 k (s , r) 
      = ruleList r 
      >>= return ∘ map-filter (isValid s k) (addUnbound s k)
      where
        addUnbound : ℕ → RTerm ⊥ → Lst → Lst
        addUnbound s k (e , l) = (ℕmap.alter (maybe just (just k)) s e , l)

        toBool : ∀{a}{A : Set a} → Dec A → Bool
        toBool (yes _) = true
        toBool (no  _) = false

        isValid : ℕ → RTerm ⊥ → Lst → Bool
        isValid s k (e , l) = toBool (ℕmap.lkup s e ≟2 just k)
          where
            _≟2_ : (a₁ a₂ : Maybe (RTerm ⊥)) → Dec (a₁ ≡ a₂)
            _≟2_ a b = Eq.cmp eq-Maybe a b
     
    -- Looks up a term given a list of instantiations.
    -- This is not, by far, a lookup function. We're just adding all possibilities together.
    lkup-inst : RTerm ⊥ → List (ℕ × List Rule) → L (List Lst)
    lkup-inst t [] = return []
    lkup-inst t rs = mapM (lkup-inst1 t) rs >>= return ∘ concat 

    -- Looks a list of RTerms in their respecive cells.
    {-# TERMINATING #-}
    lkup-list : List (RTerm ⊥ × Cell)
              → L (List Lst)
    lkup-list [] = return []
    lkup-list ((t , (d , mh) , bs) ∷ ts) 
      = lkup-aux t (Fork (((d , mh) , bs) ∷ []))
      >>= λ s₁ → (reader-local (_++_ s₁) $ lkup-list ts)
      >>= return ∘ (_++_ s₁)

    lkup-aux : RTerm ⊥ → RTrie → L (List Lst)
    lkup-aux _ (Leaf r) = ruleList r
    lkup-aux k (Fork (((d , rs) , bs) ∷ [])) 
      = let tid , tr = out k
      in lkup-inst k bs
      -- If tid ∉ mh, we run the lookup again, but in the default branch.
      -- Otherwise, we run a lkup-list.
      >>= λ r → maybe (lkup≡just tr) (lkup-aux k d) (IdxMap.lkup tid rs)
      >>= return ∘ (_++_ r)
      where
        lkup≡just : List (RTerm ⊥) → RTrie → L (List Lst)
        lkup≡just [] (Leaf r) = ruleList r
        lkup≡just _  (Leaf _) = return []
        lkup≡just tr (Fork ms) = lkup-list (zip tr ms)

    lkup-aux _ _ = trie-err "lkup-aux takes 1-cell forks"

  -- Interfacing
  lookup : RTerm ⊥ → RTrie → List (ℕmap.to (RTerm ⊥) × Name)
  lookup t bt = accept (Prelude.map Lst-open (lkup-aux t bt (Lst-empty ∷ [])))
    where
      accept : ∀{a}{A : Set a} → List (A × Maybe Name) → List (A × Name)
      accept [] = []
      accept ((a , just b) ∷ hs) = (a , b) ∷ accept hs
      accept (_ ∷ hs)            = accept hs
