module Set.MRSystems where

open import Set.Automata
open import Data.Sum
open import Data.Product
open import Function using (_∘_; id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)

private
  variable
    A B C D E F I O : Set

record MR2 (A B : Set) : Set₁ where
  eta-equality
  field
    f : A → B
    ϕ : ∀ {X} → X → (A → X)

  ϕf = ϕ {X = B}
  ϕf∘f = ϕf ∘ f

open MR2

record MR1 (A B : Set) : Set₁ where
  eta-equality
  field
    arr : A → B

open MR1

d0 : MR1 A B → MR2 A B
d0 mr1 = record 
  { f = arr mr1
  ; ϕ = λ x a → x 
  } 

d1 : MR1 A B → MR2 A B
d1 mr1 = record 
  { f = arr mr1
  ; ϕ = λ x → {!   !}
  } 

s1 : MR2 A B → MR1 A B
s1 x = record { arr = f x }

s2 : MR2 A B → MR1 A (A → B)
s2 x = record { arr = λ a → ϕf∘f x a }

k : MR2 A B → MR1 A B
k mr2 = record { arr = λ x → mr2.ϕf∘f x x }
  where module mr2 = MR2 mr2