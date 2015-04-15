open import Prelude

open import Level using (Level; _⊔_) renaming (suc to ls; zero to lz)

open import RW.Language.FinTerm

module RW.Data.BTrie where

  record IsTrie (t : Set) : Set1 where
    field
      Idx : Set
      idx≡ : Eq Idx

      toSym   : Idx → Maybe ℕ 
      fromSym : ℕ   → Maybe Idx

      inₜ   : Idx × (List t) → t
      outₜ  : t → Idx × (List t)

  open IsTrie

  -- open import RW.Data.PMap (Idx)


  data BRule (t c : Set){{pT : IsTrie t}} : Set where
    Gr : ℕ     → BRule t c
    Tr : ℕ → ℕ → BRule t c
    Fr : ℕ → c → BRule t c
    
  mutual
    Cell : (t c : Set){{pT : IsTrie t}} 
         → Set
    Cell t c {{pT}}
      = to (BTrie t c) 
      × List (ℕ × List (BRule t c))
      where
        open import RW.Data.PMap (IsTrie.Idx pT) {{IsTrie.idx≡ pT}}

    data BTrie (t c : Set){{pT : IsTrie t}} : Set where
        Fork : List (Cell t c)  → BTrie t c
        Leaf : List (BRule t c) → BTrie t c

  BTrieEmpty : {t c : Set}{{pT : IsTrie t}}
             → BTrie t c
  BTrieEmpty {{pT}} = Fork $ []
    where 
      open import RW.Data.PMap (IsTrie.Idx pT) {{IsTrie.idx≡ pT}}
