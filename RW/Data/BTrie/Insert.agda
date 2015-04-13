open import Prelude

open import Level using (_⊔_; Lift; lift) renaming (suc to ls; zero to lz)
open import Data.String using (String)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)

open import RW.Data.BTrie

module RW.Data.BTrie.Insert (t c : Set){{pT : IsTrie t}}
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

  I : ∀{a} → Set a → Set a
  I {a} = STₐ {lz} {a} (Σ ℕ (λ _ → Maybe ℕ)) 

  _<$>_ : ∀{a}{A B : Set a} → (A → B) → I A → I B
  f <$> ix = ix >>= (return ∘ f)

  --------------------
  -- Monadic boilerplate
  private
    getLbl : I (Maybe ℕ)
    getLbl = getₐ >>= return ∘ p2

    putLbl : ℕ → I Unit
    putLbl n = getₐ >>= λ x → putₐ (p1 x , just n)

    getCount : I ℕ
    getCount = p1 <$> getₐ

    putCount : ℕ → I Unit
    putCount x = getLbl >>= putₐ ∘ (_,_ x)

    ++count : I ℕ
    ++count = getCount <>= (putCount ∘ suc)

    CellCtx : Set _
    CellCtx = BTrie t c → Cell t c

    singleton : ∀{a}{A : Set a} → A → List A
    singleton x = x ∷ []

  applyBRule : BRule t c → ℕ → Maybe ℕ
  applyBRule (Tr m n) k with m ≟-ℕ k
  ...| yes _ = just n
  ...| no  _ = nothing
  applyBRule _ _ = nothing

  -- |Makes a new rule *without* checking anything.
  --  If the current label is nothing, returns a Gather
  --  If the current label is a (just l), return a Tr l.
  --
  --  Changes the state to the newly created label.
  makeRule : I (BRule t c)
  makeRule = getLbl
         >>= λ l → (++count <>= putLbl) -- increments the counter and set's it.
         >>= λ c′ → return $ maybe (flip Tr c′) (Gr c′) l

  
  -- |Given a list of rules, which arise from we reaching 
  --  either a leaf node or a previously bound symbol,
  --  will apply one of such rules or create a new one.
  --
  --  In any case, this will change the current label either
  --  to a fresh one or by a transition in the list.
  handleRules : List (BRule t c) → I (List (BRule t c))
  handleRules rs = getLbl >>= maybe (flip l≡just rs) (l≡nothing rs)
    where
      l≡just : ℕ → List (BRule t c) → I (List (BRule t c))
      l≡just l [] = singleton <$> makeRule
      l≡just l (r ∷ rs) with applyBRule r l
      ...| just l′ = putLbl l′ >> return (r ∷ rs)
      ...| nothing = (_∷_ r) <$> l≡just l rs

      l≡nothing : List (BRule t c) → I (List (BRule t c))
      l≡nothing [] = singleton <$> makeRule
      l≡nothing ((Gr k) ∷ rs) = putLbl k >> return ((Gr k) ∷ rs)
      l≡nothing (r ∷ rs)      = _∷_ r <$> l≡nothing rs

  
  -- |Given a cell and a NON-BINDING index, mIdx takes care
  --  of finding the trie we need to keep traversing and
  --  creating a reconstruction function, for when we
  --  finish modifying the mentioned trie.
  mIdx : Cell t c → IsTrie.Idx pT 
       → I (CellCtx × BTrie t c )
  mIdx (mh , bs) tid 
    = let mh′ , prf = Imap.alterPrf BTrieEmpty tid mh
    in return $ (λ f → Imap.insert tid f mh , bs) 
              , (Imap.lkup' tid mh′ prf)

  -- |When we find a binding symbol, however, things can be a bit more tricky.
  --  This symbol is either registered, in which case we just add a fresh
  --  rule to it, or it is not registered in the map, where we add it with
  --  a fresh rule.
  mSym : Cell t c → ℕ
       → I (CellCtx × BTrie t c )
  mSym (mh , bs) tsym with ℕmap.lkup tsym bs
  ...| nothing = makeRule
             >>= λ r → return (const (mh , (tsym , r ∷ []) ∷ bs) , BTrieEmpty)
  ...| just rs = handleRules rs
             >>= λ r → return (const (mh , ℕmap.insert tsym r bs) , BTrieEmpty)

  -- |𝑴 chooses which traversal function to use.
  𝑴 : Cell t c → IsTrie.Idx pT → I (CellCtx × BTrie t c)
  𝑴 c tid with IsTrie.toSym pT tid
  ...| nothing = mIdx c tid
  ...| just s  = mSym c s

  -- |Insertion of an (opened) term in a cell. Returns the altered cell.
  mutual
    insCell* : List t → List (Cell t c) → I (List (Cell t c))
    insCell* [] _ = return []
    insCell* _ [] = return []
    insCell* (t ∷ ts) (b ∷ bs)
      = insCell (outₜ t) b >>= λ b′ → (_∷_ b′) <$> insCell* ts bs

    insCell*ε : List t → I (List (Cell t c))
    insCell*ε [] = return []
    insCell*ε (t ∷ ts) 
      = insCell (outₜ t) (Imap.empty , [])
      >>= λ b → (_∷_ b) <$> insCell*ε ts
  
    {-# TERMINATING #-}
    insCell : IsTrie.Idx pT × List t → Cell t c → I (Cell t c)
    insCell (tid , tr) cell
      = 𝑴 cell tid
      >>= λ { (c , bt) → insCellAux tid tr bt >>= return ∘ c }
      where
        tr≡[] : IsTrie.Idx pT → I (BTrie t c)
        tr≡[] tid with IsTrie.toSym pT tid
        ...| nothing = (Leaf ∘ singleton) <$> makeRule
        ...| _       = return $ Fork []

        insCellAux : IsTrie.Idx pT → List t → BTrie t c 
                   → I (BTrie t c)
        insCellAux tid _  (Leaf r) = return (Leaf r)
        insCellAux tid [] _        = tr≡[] tid
        insCellAux tid tr (Fork []) 
          = Fork <$> insCell*ε tr
        insCellAux tid tr (Fork ms)
          = Fork <$> insCell* tr ms
          
  -- |Insertion has to begin in a 1-cell fork.
  ins : t → BTrie t c → I (BTrie t c)
  ins t (Fork (cell ∷ []))
    = (Fork ∘ singleton) <$> insCell (outₜ t) cell
  ins t (Fork [])
    = (Fork ∘ singleton) <$> insCell (outₜ t) (Imap.empty , [])
  ins t _ = trie-err "Insertion has to begin in a 1-cell fork"

  {-# TERMINATING #-}
  insert : c → t → (ℕ × BTrie t c) → (ℕ × BTrie t c)
  insert d term (n , Leaf r) = trie-err "Can't insert in a leaf"
  insert d term (n , bt)
    = let bt′ , n′ , lbl = STₐ.run (ins term bt) (n + 1 , nothing)
      in maybe′ (λ l′ → l′ , substΣ l′ d bt′) 
                (trie-err "empty final lbl")  lbl
    where
      open import Data.Maybe using (maybe′)

      sR : ℕ → c → BRule t c → BRule t c
      sR k c (Tr m n) with n ≟-ℕ k
      ...| yes _ = Fr m c
      ...| no  _ = Tr m n
      sR _ _ r = r

      mutual
        sC : ℕ → c → Cell t c → Cell t c
        sC k c (mh , bs) = Imap.map (substΣ k c) mh 
                         , ℕmap.map (Prelude.map (sR k c)) bs

        substΣ : ℕ → c → BTrie t c → BTrie t c
        substΣ k c (Leaf rs) = Leaf (Prelude.map (sR k c) rs)
        substΣ k c (Fork ms) = Fork (Prelude.map (sC k c) ms)
      
