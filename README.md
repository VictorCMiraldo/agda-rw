# agda-rw

This is the place where (more or less) stable releases of my RW library will be published.
For a more in-depth description of what's going on, please check my [main repo](https://github.com/VictorCMiraldo/msc-agda-tactics).

The *RW* lib
============

For those that are tired of writing `subst` and `cong` whose first argument is a horrible
lambda abstraction, there might be a solution in the horizon. This library is mainly targeted
at my [Relational Algebra library](https://github.com/VictorCMiraldo/msc-agda-tactics/tree/master/Agda/Rel),
but has shown motivating results with Agda's Propositional Equality.

by tactic
---------

Here's an excerpt from a simple [case study](https://github.com/VictorCMiraldo/msc-agda-tactics/blob/master/Agda/Rel/CaseStudies/Simple1.agda) where we prove that the `twice` function satisfies the `even` predicate as
a pre and post condition.

    twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
    twiceIsEven
      = begin
        twiceR ∙ evenR ⊆ evenR ∙ twiceR
      ⇐⟨ (tactic (by (quote evenLemma))) ⟩
        twiceR ∙ evenR ⊆ (ρ twiceR) ∙ twiceR
      ⇐⟨ (tactic (by (quote ρ-intro))) ⟩
        twiceR ∙ evenR ⊆ twiceR
      ⇐⟨ (tactic (by (quote ∙-id-r))) ⟩
        twiceR ∙ evenR ⊆ twiceR ∙ Id
      ⇐⟨ ∙-monotony ⟩
        (twiceR ⊆ twiceR × evenR ⊆ Id)
      ⇐⟨ (λ _ → ⊆-refl , φ⊆Id) ⟩
        Unit
      ∎
      
And below you'll find the same proof without using the `by` tactic.

    twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
    twiceIsEven
      = begin
        twiceR ∙ evenR ⊆ evenR ∙ twiceR
      ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x ∙ twiceR) (≡r-promote evenLemma)  ⟩
        twiceR ∙ evenR ⊆ (ρ twiceR) ∙ twiceR
      ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-promote (ρ-intro twiceR))  ⟩
        twiceR ∙ evenR ⊆ twiceR
      ⇐⟨ subst (λ x → twiceR ∙ evenR ⊆ x) (≡r-sym (≡r-promote (∙-id-r twiceR)))  ⟩
        twiceR ∙ evenR ⊆ twiceR ∙ Id
      ⇐⟨ ∙-monotony ⟩
        (twiceR ⊆ twiceR × evenR ⊆ Id)
      ⇐⟨ (λ _ → ⊆-refl , φ⊆Id) ⟩
        Unit
      ∎
      
by* tactic
----------

Sometimes, however, we apply a number of rewrites simoultaneously when we write pen and paper
Mathematics. The `by*` tactic does exactly that. Given a list of actions to be applied, it will
try to figure out where you plan to use those definitions (that is, finding the intermediate goals) 
and will call the same backend as `by` for all of them. They are joined together using
some sort of transitivity, to be provided by the user.

Below is an excerpt of `RW.Strategy.PropEq`, where we define `by*-≡`.

    open import RW.RW (≡-strat ∷ [])
    
    by*-≡ : by*-tactic
    by*-≡ = by* (quote trans)
    
And here is some usage example. Note that some situations are very slow to run the first time.
In this specific example we can easily wee why. The actions are expecting two and three arguments,
respectively. The goal-searching will try to apply these actions *everywhere* in the term,
with all possible scenarios for these arguments. The process halts when it finds a chain
that connects the goals given by `quoteGoal`.
    
    f : (x y : ℕ) → (x + y) + 0 ≡ y + (x + 0)
    f x y = tactic (by*-≡ (quote +-comm ∷ quote +-assoc ∷ []))
    
Another example, with a better runtime, follows.

    g : {A B C : Set}(S : Rel A B)(R : Rel B C)
      → (R ∙ S) ᵒ ≡r (S ᵒ ∙ Id) ∙ R ᵒ
    g S R = tactic (by*-≡r (quote ᵒ-∙-distr ∷ quote ∙-id-r ∷ []))
    
The only difference between `by*-≡` and `by*-≡r` is the transitivity they use. Although
slow, in general, both snippets typecheck.

The *auto* tactic
-----------------

We also provide an automatic tactic, that will try to figure out which term to use to prove
the given goal, given a term database. This database is defined using a Term Trie (We will
skip its explanation for it is a lengthy one, we forward the interested reader to [this](https://github.com/VictorCMiraldo/msc-agda-tactics/tree/master/Thesis) thesis, section 5.2).

For performance constraints, we strongly advise people to define their databases in a **separate**
file, using the *unquote (quoteTerm ...)* trick to force normalization. Let's assume we have
the following database, in the module TrieObj

    myTrie : RTrie
    myTrie = unquote ∘ quoteTerm ∘ p2
           $ add-action (quote ∙-assocl)
           $ add-action (quote ∙-assocr)
           $ add-action (quote ∙-assoc)
           $ add-action (quote ∙-assoc-join)
           $ add-action (quote ᵒ-idp)
           $ add-action (quote ᵒ-∙-distr)
           $ add-action (quote ∙-id-l)
           $ add-action (quote ∙-id-r)
           $ add-action (quote ρ-intro)
           $ 0 , BTrieEmpty
           
We could prove the twiceIsEven lemma in the following manner:

First we open the `Auto` module, which is inside `RW.RW`. It takes two parameters. First
the term database, and the later a function manipulating `RTermName`s, which will receive
the relation which is the goal's head and should return the relation we need to use to build
the search term. In our case, we are only searching for relational equality[^1].

    open Auto myTrie (λ _ → (rdef $ quote _≡r_))

    twiceIsEven : (twiceR ∙ evenR ⊆ evenR ∙ twiceR) ⇐ Unit
    twiceIsEven 
      = begin
        twiceR ∙ evenR ⊆ evenR ∙ twiceR
      ⇐⟨ (tactic (by (quote evenLemma))) ⟩
        twiceR ∙ evenR ⊆ (ρ twiceR) ∙ twiceR
      ⇐⟨ (tactic auto) ⟩
        twiceR ∙ evenR ⊆ twiceR
      ⇐⟨ (tactic auto ) ⟩
        twiceR ∙ evenR ⊆ twiceR ∙ Id
      ⇐⟨ (λ x → ∙-mono (p1 x) (p2 x)) ⟩
        (twiceR ⊆ twiceR × evenR ⊆ Id)
      ⇐⟨ (λ _ → ⊆-refl , φ⊆Id) ⟩
        Unit
      ∎

[^1]: This opens up an interesting future work option. We could allow that function to
return a list of names, and search them all!

Using *RW*
==========

Installation
------------

The installation process should be pretty simple. Just clone the repo and add the root
to your Agda's search path.

Imports
-------

Assuming you want to work with Agda's propositional equality reasoning, for which
there is already a strategy available, an illustration code follows:

    
    open import Data.List
    
    open import RW.Strategy.PropEq
    open import RW.RW (≡-strat ∷ [])
    
    ++-assoc : ∀{a}{A : Set a}(xs ys zs : List A)  
             → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs       = refl
    ++-assoc (x ∷ xs) ys zs = tactic (by (quote ++-assoc))
    

Implementing Your Strategy
--------------------------

In order to implement your own stratey, you need to be familiar with a couple definitions.
To keep it short, I'll just include what you might encounter immediatly when trying to
develp a custom strategy.

As of the 9th of February of 2015, the *main* function is `RWerr`:

    RWerr : Name → RWData → Err StratErr AgTerm
    RWerr act d
        =   runUStrats d
        >>= runTStrats db d act
        >>= return ∘ R2AgTerm
        
One can see that it starts by running Unification strategies (`runUStrats`) on a given
object of type `RWData` that we don't really need right now. In fact, Unification strategies
are hardcoded and are a bit more complicated to hack.

Then, we'll try to run a database (`db`) of Term strategies (`runTStrats`). Your custom
strategy is gonna be an element of `db`.

Keeping it short, you need to provide an object of type `TStrat` and pass it as a
module parameter, just like `≡-strat` on the first example. The relevant data and
record definition follows:

    record TStrat : Set where
        field
          when : RTermName → RTermName → Bool
          how  : Name → UData → Err StratErr (RTerm ℕ)

    data Trs : Set where
      Symmetry : Trs

    record UData : Set where
      constructor u-data
      field
        -- We should have an abstraction available,
        □ : RTerm Unit

        -- A substitution
        σ : RSubst
        
        -- A few transformations that might need to be applied.
        trs : List Trs
        
For example, [≡-strat](https://github.com/VictorCMiraldo/agda-rw/blob/master/RW/Strategy/PropEq.agda) 
is an instance of `TStrat`. The `when` predicate receives the names corresponding to the goal and action head, respectively.
It is pretty straight-forward on what it does. Nevertheless, the `how` is the tricky part.
You will have to transform a `UData` into a single `RTerm ℕ` that will solve the goal.
An abstraction and substitution is given to you, together with a list of transformations that might
need to be applied to the action. For now, we only handle symmetry.
A different example of a `TStrat` can be found [here](https://github.com/VictorCMiraldo/msc-agda-tactics/blob/master/Agda/Rel/Reasoning/RelEq-Strategy.agda).


Disclaimer
----------

As this is an academic project, all of this code is subject to change without previous notice.
Comments, sugestions and bug reports are more than welcome!
