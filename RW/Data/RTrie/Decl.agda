open import Prelude

module RW.Data.RTrie.Decl where

  open import RW.Language.RTerm public
  open import RW.Language.RTermIdx public
  open import RW.Data.PMap (RTermᵢ ⊥) as IdxMap

  data Rule : Set where
    Gr : ℕ     → Rule
    Tr : ℕ → ℕ → Rule
    Fr : ℕ → Name → Rule
    
  mutual
    Cell : Set
    Cell = IdxMap.to RTrie default     -- Map from indexes to tries,
         × List (ℕ × List Rule) -- Binding symbols,

    data RTrie : Set where
        Fork : List Cell → RTrie
        Leaf : List Rule → RTrie

  BTrieEmpty : RTrie
  BTrieEmpty = Fork $ []
