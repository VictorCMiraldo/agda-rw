open import Prelude
open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.RTermIdx
open import RW.Data.RTrie

open import RW.Strategy using (Trs; Symmetry; UData; u-data)

module RW.Language.RTermTrie where

  open import RW.Utils.Monads
  open Monad {{...}}

  add-action : Name → ℕ × RTrie → ℕ × RTrie
  add-action act bt
    = let
      ty = lift-ivar $ typeResult $ Ag2RType $ type act
    in insertTerm act ty bt

  replicateM : {A : Set} → List (Maybe A) → Maybe (List A)
  replicateM [] = just []
  replicateM (nothing ∷ _)  = nothing
  replicateM (just x  ∷ xs) with replicateM xs
  ...| just xs' = just (x ∷ xs')
  ...| nothing  = nothing

  postulate
    not-found       : Name × UData
    ul-is-nothing   : Name × UData

  search-action : RTermName → RBinApp ⊥ → RTrie → List (Name × UData)
  search-action hd (_ , g₁ , g₂) trie 
    = let g□ = g₁ ∩↑ g₂
          u₁ = g□ -↓ g₁
          u₂ = g□ -↓ g₂
          ul = replicateM (u₁ ∷ u₂ ∷ [])
    in maybe (mkSearch g□) (ul-is-nothing ∷ []) ul
    where
      convert : RTerm (Maybe ⊥) → List (ℕ × RTerm ⊥) × Name → Name × UData
      convert g□ (ns , act) = act , u-data (⊥2UnitCast g□) ns []

      convert-sym : RTerm (Maybe ⊥) → List (ℕ × RTerm ⊥) × Name → Name × UData
      convert-sym g□ (ns , act) = act , u-data (⊥2UnitCast g□) ns (Symmetry ∷ [])

      mkLkup : List (RTerm ⊥) → Maybe (List (List (ℕ × RTerm ⊥) × Name))
      mkLkup ul with lookupTerm (rapp hd ul) trie
      ...| [] = nothing
      ...| l  = just l

      mkSearch : RTerm (Maybe ⊥) → List (RTerm ⊥) → List (Name × UData)
      mkSearch g□ ul with mkLkup ul
      ...| just l = map (convert g□) l
      ...| nothing with mkLkup (reverse ul)
      ...| nothing = not-found ∷ []
      ...| just l  = map (convert-sym g□) l
