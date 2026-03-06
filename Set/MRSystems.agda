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

fc : MR1 A B → MR2 A B
fc mr1 = record 
  { f = arr mr1
  ; ϕ = λ x a → x 
  } 

ff : MR1 A B → MR2 A B
ff mr1 = record 
  { f = arr mr1
  ; ϕ = λ x → arr mr1
  } 

l2 : MR2 A B → MR1 A B
l2 x = record { arr = f x }

r2 : MR2 A B → MR1 A (A → B)
r2 x = record { arr = λ a → ϕ∘f x a }

k : MR2 A B → MR1 A B
k mr2 = record { arr = λ x → mr2.ϕ∘f x x }
  where module mr2 = MR2 mr2

i : {A : Set} → MR1 A A 
i {A} = record { arr = id }

-- simplicial identities
fc∘i≡ff∘i : ∀ {x : A} → (fc ∘ i) x ≡ (ff ∘ i) x
fc∘i≡ff∘i t = ?

l2∘ff≡fc∘l2 : ∀ x → arr ((k ∘ fc) x) ≡ arr x
l2∘ff≡fc∘l2 t = refl

l2∘fc≡1 : ∀ (x : Set) p q → ϕ (fc (i {x})) p q ≡ p
l2∘fc≡1 x p q = refl

k∘ff≡1 : ∀ (x : Set) p q → ϕ (ff (i {x})) p q ≡ q
k∘ff≡1 x p q = refl

-- r2∘fc≡fc∘k
-- r2∘fc≡fc∘k
-- 
-- r2∘ff≡1