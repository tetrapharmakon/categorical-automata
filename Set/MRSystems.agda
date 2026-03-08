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

mkMR1 : (u : A → B) → MR1 A B 
mkMR1 u = record { arr = u }

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

src : MR1 A B → Set
src {A} x = A

trg : MR1 A B → Set
trg {A} {B} x = B
-- simplicial identities
{-
      <--d0=src----      <-----d2=l2-----
MRS0  ---s0=mkMR1--> MRS1 ------s0=ff----> MRS2
      <--d1=trg----      <-----d1=k------
                         ------s1=fc---->
                         <-----d0=r2-----
-}

-- ff ∘ i = fc ∘ i
fc∘i≡ff∘i : ∀ {A} t → f (fc (i {A})) t ≡ f (ff (i {A})) t
fc∘i≡ff∘i t = refl

-- l2 ∘ fc = id_MRS1
l2∘fc≡1 : ∀ x → l2 (fc x) ≡ x
l2∘fc≡1 x = refl

-- k ∘ ff = id_MRS1
k∘ff≡1 : ∀ x → k (ff x) ≡ x
k∘ff≡1 x = refl

-- k ∘ fc = id_MRS1
k∘fc≡1 : ∀ x → k (fc x) ≡ x
k∘fc≡1 x = refl

-- r2 ∘ ff = id_MRS1
r2∘ff≡1 : ∀ x t → arr (r2 (ff x)) t ≡ arr x
r2∘ff≡1 x t = refl

-- l2 ∘ ff = i ∘ trg
l2∘ff≡i∘trg : ∀ x → arr (l2 (ff x)) ≡ arr x
l2∘ff≡i∘trg u = refl

-- r2 ∘ fc = i ∘ src
r2∘fc≡i∘src : ∀ x t → arr (r2 (fc x)) t ≡ arr x t
r2∘fc≡i∘src x t = refl

-- face–face identities (from the comment)
src∘k≡src∘r2 : ∀ x → src (k x) ≡ src (r2 x)
src∘k≡src∘r2 x = refl

src∘l2≡trg∘r2 : ∀ {A} {B} (x : MR2 A B) → src (l2 x) ≡ {! trg (r2 x) !}
src∘l2≡trg∘r2 x = refl

trg∘l2≡trg∘k : ∀ x → trg (l2 x) ≡ trg (k x)
trg∘l2≡trg∘k x = refl
