# agda-rw

This is the place where (more or less) stable releases of my RW library will be published.
For a more in-depth description of what's going on, please check my [main repo](https://github.com/VictorCMiraldo/msc-agda-tactics).

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

    ```agda
    open import Data.List
    
    open import RW.Strategy.PropEq
    open import RW.RW (≡-strat ∷ [])
    
    ++-assoc : ∀{a}{A : Set a}(xs ys zs : List A)  
             → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs       = refl
    ++-assoc (x ∷ xs) ys zs = tactic (RW (quote ++-assoc))
    ```

Implementing Your Strategy
--------------------------

*todo*

