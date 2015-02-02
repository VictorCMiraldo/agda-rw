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
    ≡-when : RTermName → RTermName → Bool
    ≡-when pat-≡ pat-≡ = true
    ≡-when _     _     = false

    ≡-how : Name → RTerm (Maybe ℕ) → RSubst → Err StratErr (RTerm ℕ)
    ≡-how act g□ σ = i2 (rapp (rdef (quote cong))
                              ( hole2Abs g□
                              ∷ makeApp act σ
                              ∷ [])
                        )

  ≡-strat : TStrat
  ≡-strat = record
    { when = ≡-when
    ; how  = ≡-how
    }
