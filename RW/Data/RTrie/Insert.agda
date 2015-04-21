open import Prelude

open import Level using (_⊔_; Lift; lift) renaming (suc to ls; zero to lz)
open import Data.String using (String)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)

module RW.Data.RTrie.Insert
    where

  open import Relation.Binary.PropositionalEquality
    using (inspect; [_])

  open import RW.Data.RTrie.Decl
  import RW.Data.PMap (RTermᵢ ⊥) as IdxMap
  import RW.Data.PMap ℕ as ℕmap

  postulate 
    trie-err : ∀{a}{A : Set a} → String → A 
  
  open import RW.Utils.Monads
  open Monad {{...}}
  open Eq {{...}}

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
    CellCtx = RTrie → Cell

    singleton : ∀{a}{A : Set a} → A → List A
    singleton x = x ∷ []

  applyBRule : Rule → ℕ → Maybe ℕ
  applyBRule (Tr m n) k with m ≟-ℕ k
  ...| yes _ = just n
  ...| no  _ = nothing
  applyBRule _ _ = nothing

  -- |Makes a new rule *without* checking anything.
  --  If the current label is nothing, returns a Gather
  --  If the current label is a (just l), return a Tr l.
  --
  --  Changes the state to the newly created label.
  makeRule : I Rule
  makeRule = getLbl
         >>= λ l → (++count <>= putLbl) -- increments the counter and set's it.
         >>= λ c′ → return $ maybe (flip Tr c′) (Gr c′) l

  
  -- |Given a list of rules, which arise from we reaching 
  --  either a leaf node or a previously bound symbol,
  --  will apply one of such rules or create a new one.
  --
  --  In any case, this will change the current label either
  --  to a fresh one or by a transition in the list.
  handleRules : List Rule → I (List Rule)
  handleRules rs = getLbl >>= maybe (flip l≡just rs) (l≡nothing rs)
    where
      l≡just : ℕ → List Rule → I (List Rule)
      l≡just l [] = singleton <$> makeRule
      l≡just l (r ∷ rs) with applyBRule r l
      ...| just l′ = putLbl l′ >> return (r ∷ rs)
      ...| nothing = (_∷_ r) <$> l≡just l rs

      l≡nothing : List Rule → I (List Rule)
      l≡nothing [] = singleton <$> makeRule
      l≡nothing ((Gr k) ∷ rs) = putLbl k >> return ((Gr k) ∷ rs)
      l≡nothing (r ∷ rs)      = _∷_ r <$> l≡nothing rs

  
  -- |Given a cell and a NON-BINDING index, mIdx takes care
  --  of finding the trie we need to keep traversing and
  --  creating a reconstruction function, for when we
  --  finish modifying the mentioned trie.
  mIdx : Cell → RTermᵢ ⊥ 
       → I (CellCtx × RTrie)
  -- In the case we are inserting a ivarᵢ, we are going to merge the new btrie,
  -- which is going to be a leaf (TODO: why?), in the default branch.
  mIdx ((d , mh) , bs) (ivarᵢ _)
    = return $ (λ bt → (merge d bt , mh) , bs) , BTrieEmpty
    where
      merge : RTrie → RTrie → RTrie
      merge (Leaf as) (Leaf bs) = Leaf (as ++ bs)
      merge _ bt                = bt 
  -- For the more general case, if tid ∉ mh, we add and entry (tid ↦ empty).
  -- After, we return mh(tid) and the context that modifies this exact entry.
  mIdx ((d , mh) , bs) tid
    = let mh′ , prf = IdxMap.alterPrf BTrieEmpty tid mh
    in return $ (λ f → (d , IdxMap.insert tid f mh) , bs) 
              , (IdxMap.lkup' tid mh′ prf)

  -- |When we find a binding symbol, however, things can be a bit more tricky.
  --  This symbol is either registered, in which case we just add a fresh
  --  rule to it, or it is not registered in the map, where we add it with
  --  a fresh rule.
  mSym : Cell → ℕ
       → I (CellCtx × RTrie)
  mSym (mh , bs) tsym with ℕmap.lkup tsym bs
  ...| nothing = makeRule
             >>= λ r → return (const (mh , (tsym , r ∷ []) ∷ bs) 
                              , BTrieEmpty)
  ...| just rs = handleRules rs
             >>= λ r → return (const (mh , ℕmap.insert tsym r bs) 
                              , BTrieEmpty)

  -- |𝑴 chooses which traversal function to use.
  𝑴 : {A : Set}{{enA : Enum A}} 
     → Cell → RTermᵢ A → I (CellCtx × RTrie)
  𝑴 {{enum aℕ _}} c tid with toSymbol tid | inspect toSymbol tid
  ...| nothing | [ prf ] = mIdx c (idx-cast tid prf)
  ...| just s  | _       = maybe (mSym c) enum-err (aℕ s)
    where postulate enum-err : I (CellCtx × RTrie)

  -- |Insertion of an (opened) term in a cell. Returns the altered cell.
  mutual
    insCell* : {A : Set}{{enA : Enum A}} 
             → List (RTerm A) → List Cell → I (List Cell)
    insCell* [] _ = return []
    insCell* _ [] = return []
    insCell* (t ∷ ts) (b ∷ bs)
      = insCell (out t) b >>= λ b′ → (_∷_ b′) <$> insCell* ts bs

    -- Variation of insCell*, assuming we're always adding to empty cells.
    insCell*ε : {A : Set}{{enA : Enum A}} → List (RTerm A) → I (List Cell)
    insCell*ε [] = return []
    insCell*ε (t ∷ ts) 
      = insCell (out t) ((Leaf [] , IdxMap.empty) , [])
      >>= λ b → (_∷_ b) <$> insCell*ε ts
  
    {-# TERMINATING #-}
    insCell : {A : Set}{{enA : Enum A}} 
            → RTermᵢ A × List (RTerm A) → Cell → I Cell
    insCell (tid , tr) cell
      = 𝑴 cell tid
      >>= λ { (c , bt) → insCellAux tid tr bt >>= return ∘ c }
      where
        -- Note how if tid is a binding symbol, we don't do anything. That's
        -- because 𝑴 already took care of adding the rules in the correct place for us.
        tr≡[] : {A : Set}{{enA : Enum A}} 
              → RTermᵢ A → I RTrie
        tr≡[] tid with toSymbol tid
        ...| nothing = (Leaf ∘ singleton) <$> makeRule
        ...| _       = return $ Fork []

        insCellAux : {A : Set}{{enA : Enum A}} 
                   → RTermᵢ A → List (RTerm A) → RTrie 
                   → I RTrie
        -- Inserting in a Leaf is impossible...
        insCellAux tid _  (Leaf r) = return (Leaf r)
        -- If we don't have recursive arguments in the term beeing inserted, 
        -- we follow by tr≡[]
        insCellAux tid [] _        = tr≡[] tid
        -- Otherwise we simply add our recursive arguments.
        insCellAux tid tr (Fork []) 
          = Fork <$> insCell*ε tr
        insCellAux tid tr (Fork ms)
          = Fork <$> insCell* tr ms
          
  -- |Insertion has to begin in a 1-cell fork.
  --  This gives some intuition that BTries should contain an arity, somewhere in their type.
  ins : {A : Set}{{enA : Enum A}} → RTerm A → RTrie → I RTrie
  ins t (Fork (cell ∷ []))
    = (Fork ∘ singleton) <$> insCell (out t) cell
  ins t (Fork [])
    = (Fork ∘ singleton) <$> insCell (out t) ((Leaf [] , IdxMap.empty) , [])
  ins t _ = trie-err "Insertion has to begin in a 1-cell fork"

  -- Interfacing
  {-# TERMINATING #-}
  insertTerm : {A : Set}{{enA : Enum A}} → Name → RTerm A → (ℕ × RTrie) → (ℕ × RTrie)
  insertTerm d term (n , Leaf r) = trie-err "Can't insert in a leaf"
  insertTerm d term (n , bt)
    = let bt′ , n′ , lbl = STₐ.run (ins term bt) (n + 1 , nothing)
      in maybe′ (λ l′ → l′ , substΣ l′ d bt′) 
                (trie-err "empty final lbl")  lbl
    where
      open import Data.Maybe using (maybe′)

      -- Substitution boilerplate.

      sR : ℕ → Name → Rule → Rule
      sR k c (Tr m n) with n ≟-ℕ k
      ...| yes _ = Fr m c
      ...| no  _ = Tr m n
      sR _ _ r = r

      mutual
        sC : ℕ → Name → Cell → Cell
        sC k c ((d , mh) , bs) 
          = (substΣ k c d 
            , IdxMap.map (substΣ k c) mh) 
          , ℕmap.map (Prelude.map (sR k c)) bs

        substΣ : ℕ → Name → RTrie → RTrie
        substΣ k c (Leaf rs) = Leaf (Prelude.map (sR k c) rs)
        substΣ k c (Fork ms) = Fork (Prelude.map (sC k c) ms)
      
