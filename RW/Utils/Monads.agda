open import Prelude
open import Level using (Level; _⊔_; Lift) renaming (zero to lz; suc to ls)
open import Data.Maybe using (Maybe; nothing; just)

module RW.Utils.Monads where

  ---------------------
  -- Monad Typeclass --
  ---------------------

  record Monad {a}(M : Set a → Set a) : Set (ls a) where
    infixl 1 _>>=_
    field
      return : {A : Set a} → A → M A
      _>>=_  : {A B : Set a} → M A → (A → M B) → M B

  open Monad {{...}}

  mapM : ∀{a}{M : Set a → Set a}{{ m : Monad M}}{A B : Set a} 
       → (A → M B) → List A → M (List B)
  mapM f []       = return []
  mapM f (x ∷ la) = f x >>= (λ x' → mapM f la >>= return ∘ _∷_ x')

  _>>_ : ∀{a}{M : Set a → Set a}{{ m : Monad M }}{A B : Set a}
       → M A → M B → M B
  f >> g = f >>= λ _ → g

  -- Binds the side-effects of the second computation,
  -- returning the value of the first.
  _<>=_ : ∀{a}{M : Set a → Set a}{{ m : Monad M }}{A B : Set a}
        → M A → (A → M B) → M A
  f <>= x = f >>= λ r → x r >> return r

  {-
  _<$>_ : ∀{a}{A B : Set a}{M : Set a → Set a}{{ m : Monad M }}
        → (A → B) → M A → M B
  f <$> x = ?
  -}

  -----------------
  -- Maybe Monad --
  -----------------

  _<$>+1_ : ∀{a}{A B : Set a} → (A → B) → Maybe A → Maybe B
  f <$>+1 x with x
  ...| nothing = nothing
  ...| just x' = just (f x')

  instance
    MonadMaybe : ∀{a} → Monad {a} Maybe
    MonadMaybe = record
      { return = just
      ; _>>=_  = λ { nothing  _ → nothing 
                   ; (just x) f → f x 
                   }
      }

  -----------------
  -- State Monad --
  -----------------

  record ST (s a : Set) : Set where
    field run : s → (a × s)

  evalST : ∀{a s} → ST s a → s → a
  evalST s = p1 ∘ (ST.run s)

  get : ∀{s} → ST s s
  get = record { run = λ s → (s , s) }

  put : ∀{s} → s → ST s Unit
  put s = record { run = λ _ → (unit , s) }

  instance
    MonadState : ∀{s} → Monad (ST s)
    MonadState = record
      { return = λ a → record { run = λ s → a , s }
      ; _>>=_  = λ x f → record { run = 
                 λ s → let y = ST.run x s
                       in ST.run (f (p1 y)) (p2 y)
                }
      }

  -- Universe Polymorphic version of the state monad.
  record STₐ {a b}(s : Set a)(o : Set b) : Set (a ⊔ b) where
    field run : s → (o × s)

  evalSTₐ : ∀{a b}{s : Set a}{o : Set b} → STₐ s o → s → o
  evalSTₐ s = p1 ∘ (STₐ.run s)

  getₐ : ∀{a}{s : Set a} → STₐ s s
  getₐ = record { run = λ s → (s , s) }

  putₐ : ∀{a}{s : Set a} → s → STₐ s Unit
  putₐ s = record { run = λ _ → (unit , s) }

  instance
    MonadStateₐ : ∀{a b}{s : Set a} → Monad {a ⊔ b} (STₐ s)
    MonadStateₐ = record
      { return = λ x → record { run = λ s → x , s }
      ; _>>=_  = λ x f → record { run = 
                 λ s → let y = STₐ.run x s
                       in STₐ.run (f (p1 y)) (p2 y)
                }
      }

  -------------
  -- Fresh ℕ --
  -------------

  Freshℕ : Set → Set
  Freshℕ A = ST ℕ A

  runFresh : ∀{A} → Freshℕ A → A
  runFresh f = evalST f 0

  runFresh-n : ∀{A} → Freshℕ A → ℕ → A
  runFresh-n = evalST

  inc : Freshℕ Unit
  inc = get >>= (put ∘ suc)

  ----------------
  -- List Monad --
  ----------------

  NonDet : ∀{a} → Set a → Set a
  NonDet A = List A

  NonDetBind : ∀{a}{A B : Set a} → NonDet A → (A → NonDet B) → NonDet B
  NonDetBind x f = concat (map f x)

  NonDetRet : ∀{a}{A : Set a} → A → NonDet A
  NonDetRet x = x ∷ []

  instance
    MonadNonDet : Monad {lz} NonDet
    MonadNonDet = record
      { return = NonDetRet
      ; _>>=_  = NonDetBind
      }

  ------------------
  -- Reader Monad --
  ------------------

  Reader : ∀{a b} → Set a → Set b → Set (a ⊔ b)
  Reader R A = R → A

  reader-bind : ∀{a b}{R : Set a}{A B : Set b}
              → Reader R A → (A → Reader R B) → Reader R B
  reader-bind ra rb = λ r → rb (ra r) r

  reader-return : ∀{a b}{R : Set a}{A : Set b}
                → A → Reader R A
  reader-return a = λ _ → a

  reader-local : ∀{a b}{R : Set a}{A : Set b}
               → (R → R) → Reader R A → Reader R A
  reader-local f ra = ra ∘ f

  reader-ask : ∀{a}{R : Set a} → Reader R R
  reader-ask = id

  instance
    MonadReader : ∀{a b}{R : Set a} → Monad {b ⊔ a} (Reader {b = b ⊔ a} R)
    MonadReader = record
      { return = reader-return
      ; _>>=_  = reader-bind
      }
