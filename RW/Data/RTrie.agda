module RW.Data.RTrie where

  open import RW.Data.RTrie.Decl public
  open import RW.Data.RTrie.Insert 
    using (insertTerm) public
  open import RW.Data.RTrie.Lookup 
    renaming (lookup to lookupTerm) public
