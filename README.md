# agda-rw

This is the place where (more or less) stable releases of my RW library will be published.
For a more in-depth description of what's going on, please check my [main repo](https://github.com/VictorCMiraldo/msc-agda-tactics).

The *RW* lib
============

For those that are tired of writing `subst` and `cong` whose first argument is a horrible
lambda abstraction, there might be a solution in the horizon. This library is mainly targeted
at my [Relational Algebra library](https://github.com/VictorCMiraldo/msc-agda-tactics/tree/master/Agda/Rel),
but has shown motivating results with Agda's Propositional Equality.

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
