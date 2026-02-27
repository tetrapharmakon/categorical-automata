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
    ϕ : B → (A → B)

  ϕ∘f = ϕ ∘ f

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
  ; ϕ = λ x → arr mr1
  } 

s1 : MR2 A B → MR1 A B
s1 x = record { arr = f x }

s2 : MR2 A B → MR1 A (A → B)
s2 x = record { arr = λ a → ϕ∘f x a }

k : MR2 A B → MR1 A B
k mr2 = record { arr = λ x → mr2.ϕ∘f x x }
  where module mr2 = MR2 mr2

i : {A : Set} → MR1 A A 
i {A} = record { arr = id }

-- simplicial identities
k∘d1≡1 : ∀ x → arr ((k ∘ d1) x) ≡ arr x
k∘d1≡1 t = refl

k∘d0≡1 : ∀ x → arr ((k ∘ d0) x) ≡ arr x
k∘d0≡1 t = refl

d0∘i : ∀ (x : Set) p q → ϕ (d0 (i {x})) p q ≡ p
d0∘i x p q = refl

d1∘i : ∀ (x : Set) p q → ϕ (d1 (i {x})) p q ≡ q
d1∘i x p q = refl