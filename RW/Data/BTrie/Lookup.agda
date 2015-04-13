open import Prelude

open import Level using (_⊔_; Lift; lift) renaming (suc to ls; zero to lz)
open import Data.String using (String)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)

open import RW.Data.BTrie

module RW.Data.BTrie.Lookup (t c : Set){{pT : IsTrie t}}{{eqT : Eq t}}
    where

  postulate 
    trie-err : ∀{a}{A : Set a} → String → A 
  
  open import RW.Utils.Monads
  open Monad {{...}}
  open IsTrie {{...}}
  open Eq {{...}}

  open import RW.Data.PMap (IsTrie.Idx pT) {{IsTrie.idx≡ pT}} 
    as Imap hiding (insert)
  open import RW.Data.PMap ℕ 
    as ℕmap hiding (insert)

  -------------------------------
  -- Some type boilerplate

  Label : Set → Set
  Label a = ℕ ⊎ a

  Lst : Set
  Lst = ℕmap.to t × Maybe (Label c)

  Lst-empty : Lst
  Lst-empty = ℕmap.empty , nothing

  Lst-open : Lst → (ℕmap.to t × Maybe c)
  Lst-open (e , l) = (e , lbl-join l)
    where
      lbl-join : Maybe (Label c) → Maybe c
      lbl-join nothing = nothing
      lbl-join (just (i1 _)) = nothing
      lbl-join (just (i2 a)) = just a

  ---------------------------
  -- Lookup monad

  L : Set → Set
  L = Reader (List Lst)

  ----------------------------
  -- Rule application

  applyBRule1 : BRule t c → Lst → Lst
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

  applyBRule : BRule t c → L (List Lst)
  applyBRule r = reader-ask >>= return ∘ (Prelude.map (applyBRule1 r))
  
  ruleList : List (BRule t c) → L (List Lst)
  ruleList rs = mapM applyBRule rs >>= return ∘ concat

  ------------------------------
  -- Actual Lookup

  map-filter : ∀{a}{A B : Set a} → (B → Bool) → (A → B) → List A → List B
  map-filter p f = foldr (λ h r → let x = f h in ite (p x) (x ∷ r) r) []
    where
      ite : ∀{a}{A : Set a} → Bool → A → A → A
      ite true  t _ = t
      ite false _ e = e

  mutual
    lkup-inst1 : t → ℕ × List (BRule t c) → L (List Lst)
    lkup-inst1 k (s , r) 
      = ruleList r 
      >>= return ∘ map-filter (isValid s k) (addUnbound s k)
      where
        addUnbound : ℕ → t → Lst → Lst
        addUnbound s k (e , l) = (ℕmap.alter (maybe just (just k)) s e , l)

        toBool : ∀{a}{A : Set a} → Dec A → Bool
        toBool (yes _) = true
        toBool (no  _) = false

        isValid : ℕ → t → Lst → Bool
        isValid s k (e , l) = toBool (ℕmap.lkup s e ≟ just k)
          where
            _≟_ : (a₁ a₂ : Maybe t) → Dec (a₁ ≡ a₂)
            _≟_ a b = Eq.cmp eq-Maybe a b
            
    lkup-inst : t → List (ℕ × List (BRule t c)) → L (List Lst)
    lkup-inst t [] = return []
    lkup-inst t rs = mapM (lkup-inst1 t) rs >>= return ∘ concat 

    {-# TERMINATING #-}
    lkup-list : List (t × Imap.to (BTrie t c) × List (ℕ × List (BRule t c)))
              → L (List Lst)
    lkup-list [] = reader-ask
    lkup-list ((t , mh , bs) ∷ ts) 
      = lkup-aux t (Fork ((mh , bs) ∷ []))
      >>= λ s₁ → (reader-local (_++_ s₁) $ lkup-list ts)
      >>= return ∘ (_++_ s₁)

    lkup-aux : t → BTrie t c → L (List Lst)
    lkup-aux _ (Leaf _) = return []
    lkup-aux k (Fork ((rs , bs) ∷ [])) 
      = let tid , tr = outₜ k
      in lkup-inst k bs
      >>= λ r₁ → maybe (lkup≡just tr) (return []) (Imap.lkup tid rs)
      >>= return ∘ (_++_ r₁)
      where
        lkup≡just : List t → BTrie t c → L (List Lst)
        lkup≡just [] (Leaf r) = ruleList r
        lkup≡just _  (Leaf _) = return []
        lkup≡just tr (Fork ms) = lkup-list (zip tr ms)

    lkup-aux _ _ = trie-err "lkup-aux takes 1-cell forks"

  lookup : t → BTrie t c → List (ℕmap.to t × c)
  lookup t bt = accept (Prelude.map Lst-open (lkup-aux t bt (Lst-empty ∷ [])))
    where
      accept : ∀{a}{A : Set a} → List (A × Maybe c) → List (A × c)
      accept [] = []
      accept ((a , just b) ∷ hs) = (a , b) ∷ accept hs
      accept (_ ∷ hs)            = accept hs
