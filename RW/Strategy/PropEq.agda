open import Prelude
open import Data.Maybe using (Maybe; just; nothing)

open import RW.Language.RTerm
open import RW.Language.RTermUtils using (hole2Abs)
open import RW.Language.Unification using (RSubst)
open import RW.Utils.Error
open import RW.Strategy

module RW.Strategy.PropEq where

  pattern pat-≡  = (rdef (quote _≡_))

  private
    open UData

    ≡-when : RTermName → RTermName → Bool
    ≡-when pat-≡ pat-≡ = true
    ≡-when _     _     = false

    fixTrs : Trs → RTerm ⊥ → RTerm ⊥
    fixTrs Symmetry term = rapp (rdef (quote sym)) (term ∷ [])

    ≡-how : Name → UData → Err StratErr (RTerm ⊥)
    ≡-how act (u-data g□ σ trs)
      = i2 (rapp (rdef (quote cong))
                 ( hole2Abs g□
                 ∷ foldr fixTrs (makeApp act σ) trs
                 ∷ [])
           )

  ≡-strat : TStrat
  ≡-strat = record
    { when = ≡-when
    ; how  = ≡-how
    }
