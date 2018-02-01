open import Prelude
open import Reflection renaming (Term to AgTerm; Type to AgType)
open import Data.String using (String)

open import Data.Unit

open import RW.Language.RTerm
open import RW.Language.RTermUtils
open import RW.Language.FinTerm
open import RW.Language.GoalGuesser 1

open import RW.Strategy

module RW.RW (db : TStratDB) where

  open import RW.Utils.Monads
  open import RW.Utils.Error
  open Monad {{...}}
  open IsError {{...}}

  ------------------
  -- Housekeeping --
  ------------------

  _>>=TC_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  _>>=TC_ = bindTC 

  -- We need to bring our instances into scope explicitely,
  -- to make Agda happy.
  private
    instance
      ErrErr   = IsError-StratErr
      ErrMonad = MonadError

    unarg : {A : Set} → Arg A → A
    unarg (arg _ x) = x

  -- We need to translate types to FinTerms, so we know how many variables
  -- we're expecting to guess from instantiation.
  Ag2RTypeFin : AgType → ∃ FinTerm
  Ag2RTypeFin = R2FinType ∘ lift-ivar ∘ η ∘ Ag2RType

  -- TODO: fix the duality: "number of ivar's lifted to ovar's vs. parameters we need to guess"

  make-RWData-aux : Name → AgType → AgTerm → List (Arg AgType) → TC RWData
  make-RWData-aux act actty goal ctx with η (Ag2RTerm goal) | Ag2RTypeFin actty | map (Ag2RType ∘ unarg) ctx
  ...| g' | tyℕ , ty | ctx' with forceBinary g' | forceBinary (typeResult ty)
  ...| just g | just a = returnTC (rw-data g tyℕ a ctx')
  ...| just _ | nothing = typeError (strErr "Something strange happened with the action" ∷ [])
  ...| nothing | just _ = typeError (strErr "Something strange happened with the goal" ∷ [])
  ...| nothing | nothing = typeError (strErr "My brain just exploded." ∷ []) 


  make-RWData : Name → AgTerm → List (Arg AgType) → TC RWData
  make-RWData act goal ctx = getType act >>=TC λ ty → make-RWData-aux act ty goal ctx

  -- Given a goal and a list of actions to apply to such goal, return
  -- a list l₁ ⋯ lₙ such that ∀ 0 < i ≤ n . tyᵢ : p1 lᵢ → p1 lᵢ₊₁ 
  Ag2RTypeFin* : RTerm ⊥ → List AgType → Maybe (List (RBinApp ⊥ × ∃ (RBinApp ∘ Fin)))
  Ag2RTypeFin* (rapp n (g₁ ∷ g₂ ∷ [])) tys 
    =            mapM (return ∘ Ag2RTypeFin) tys
    >>=          mapM (λ v → forceBinary (typeResult (p2 v)) >>= (return ∘ (_,_ $ p1 v)))
    >>= λ tys' → (divideGoal (n , g₁ , g₂) tys' >>= assemble)
    >>= λ gs   → return (zip gs tys')
    where
      assemble : {A : Set} → List (RTerm A) → Maybe (List (RBinApp A))
      assemble (x1 ∷ x2 ∷ []) = just ((n , x1 , x2) ∷ [])
      assemble (x1 ∷ x2 ∷ l)  = assemble (x2 ∷ l) >>= return ∘ (_∷_ (n , x1 , x2))
      assemble _              = nothing
  Ag2RTypeFin* _ _ = nothing

  -- Produces a list of RWData, one for each 'guessed' step.
  make-RWData*-aux : List Name → List AgType → AgTerm → List (Arg AgType) → TC (List RWData)
  make-RWData*-aux acts tys goal ctx with Ag2RTerm goal | map (Ag2RType ∘ unarg) ctx
  ...| g' | ctx' with Ag2RTypeFin* g' tys
  ...| nothing = typeError (strErr "Are you sure you can apply those steps?" ∷ [])
  ...| just r  = returnTC (map (λ x → rw-data (p1 x) (p1 (p2 x)) (p2 (p2 x)) ctx') r)
  
  mapTC : ∀{a b}{A : Set a}{B : Set b}
        → (A → TC B) → List A → TC (List B)
  mapTC f [] = returnTC []
  mapTC f (x ∷ xs) = f x >>=TC λ x' → mapTC f xs >>=TC λ xs' → returnTC (x' ∷ xs')

  make-RWData* : List Name → AgTerm → List (Arg AgType) → TC (List RWData)
  make-RWData* acts goal ctx = mapTC getType acts >>=TC λ tys → make-RWData*-aux acts tys goal ctx

  postulate
    RW-error  : ∀{a}{A : Set a} → String → A
    RW-error' : ∀{a}{A : Set a} → RWData → A

  RWerr : Name → RWData → Err StratErr (RWData × UData × RTerm ⊥)
  RWerr act d
    =   runUStrats d
    >>= λ u → runTStrats db d act u
    >>= λ v → return (d , u , v)

  -- A variant with less information, more suitable to be map'ed.
  RWerr-less : Name → RWData → Err StratErr (RTerm ⊥)
  RWerr-less act d = RWerr act d >>= return ∘ p2 ∘ p2

  runErrTC : {A : Set} → Err StratErr A → TC A
  runErrTC f with runErr f
  ...| i1 err = typeError (RW-error err)
  ...| i2 res = returnTC res

  ----------------
  -- By Tactics --
  ----------------

  -- Standard debugging version.
  by' : Name → List (Arg AgType) → AgTerm → TC (RWData × UData × RTerm ⊥)
  by' act ctx goal = make-RWData act goal ctx 
                 >>=TC λ rwdata → runErrTC (RWerr act rwdata)
  
  -- This function is only beeing used to pass the context
  -- given by the 'tactic' keyword around.
  by-aux : Name → List (Arg AgType) → AgTerm → TC AgTerm
  by-aux act ctx goal = by' act ctx goal >>=TC (returnTC ∘ R2AgTerm ∘ p2 ∘ p2)

  postulate 
    RTermError : ∀{a}{A : Set a} → RTerm A → ErrorPart

  macro
    by : Name → AgTerm → TC ⊤
    by act qhole = getContext 
               >>=TC λ ctx  → inferType qhole
               >>=TC λ goal → by-aux act ctx goal 
               >>=TC λ res  → unify qhole res

    show-me : AgTerm → AgTerm → TC ⊤
    show-me u qhole = quoteTC (Ag2RTerm u)
                  >>=TC λ x → normalise x
                  >>=TC λ x' → typeError (termErr x' ∷ []) 

-- normalise u >>=TC λ u' → typeError (RTermError (Ag2RTerm u') ∷ [])

    by-dbg : Name → AgTerm → TC ⊤
    by-dbg act qhole = getContext 
               >>=TC λ ctx  → inferType qhole
               >>=TC λ goal → by' act ctx goal 
               >>=TC λ { (rwdata , udata , res) → quoteTC rwdata
               >>=TC λ rwdata' → quoteTC udata
               >>=TC λ udata' → quoteTC (R2AgTerm res)
               >>=TC λ resQ → normalise resQ
               >>=TC λ res' → typeError (termErr res' ∷ []) }

{-
  -- Handling multiple actions, naive way.
  -- by+ is pretty much foldM (<|>) error (by ⋯),
  -- where (<|>) is the usual alternative from Error Monad.
  by+ : List Name → List (Arg AgType) → AgTerm → AgTerm
  by+ [] _ _ = RW-error "No suitable action"
  by+ (a ∷ as) ctx goal with runErr (make-RWData a goal ctx >>= RWerr a)
  ...| i1 _ = by+ as ctx goal
  ...| i2 t = R2AgTerm ∘ p2 ∘ p2 $ t

  join-tr : Name → List (RTerm ⊥) → RTerm ⊥
  join-tr _  []      = ivar 0
  join-tr tr (x ∷ l) = foldr (λ h r → rapp (rdef tr) (r ∷ h ∷ [])) x l

  -- Handling multiple goals.
  by*-err : Name → List Name → List (Arg AgType) → AgTerm → Err StratErr AgTerm
  by*-err tr acts ctx goal 
    =   make-RWData* acts goal ctx 
    >>= λ l → mapM (uncurry RWerr-less) (zip acts l)
    >>= return ∘ R2AgTerm ∘ join-tr tr
    where
      unzip : {A B : Set} → List (A × B) → List A × List B
      unzip [] = [] , []
      unzip ((a , b) ∷ l) with unzip l
      ...| la , lb = a ∷ la , b ∷ lb

  by*-tactic : Set
  by*-tactic = List Name → List (Arg AgType) → AgTerm → AgTerm

  by* : Name → by*-tactic
  by* tr acts ctx goal with runErr (by*-err tr acts ctx goal)
  ...| i1 err = RW-error err
  ...| i2 res = res

  ------------------------------
  -- Adding Tries to the cake --
  ------------------------------

  -- The proper way to handle multiple actions.

  open import RW.Data.RTrie

  module Auto 
    (bt    : RTrie)                 -- which trie to use,
    (newHd : RTermName → RTermName) -- given the goal head, how to build the head for the action.
    where

    open import RW.Language.RTermTrie

    our-strategy : RTermName → Name → UData → Err StratErr (RTerm ⊥)
    our-strategy goal 
      = maybe 
        TStrat.how 
        (const $ const $ i1 no-strat) 
      $ filter-db db
      where
        no-strat : StratErr
        no-strat = NoTStrat goal (newHd goal)

        filter-db : TStratDB → Maybe TStrat
        filter-db [] = nothing
        filter-db (s ∷ ss) with TStrat.when s goal (newHd goal)
        ...| false = filter-db ss
        ...| true  = just s

    auto-internal : List (Arg AgType) → AgTerm → Err StratErr AgTerm
    auto-internal _ goal with forceBinary $ Ag2RTerm goal
    ...| nothing = i1 $ Custom "non-binary goal"
    ...| just (hd , g₁ , g₂)
      = let
        options = search-action (newHd hd) (hd , g₁ , g₂) bt
        strat   = uncurry $ our-strategy hd
        err     = Custom "No option was succesful"
      in try-all strat err options >>= return ∘ R2AgTerm
    
    auto : List (Arg AgType) → AgTerm → AgTerm
    auto ctx goal with runErr (auto-internal ctx goal)
    ...| i1 err = RW-error err
    ...| i2 r   = r
-}
