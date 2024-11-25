module Set.CrossedModules where

open import Level
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Monoid : Set (suc zero) where
  field
    Carrier : Set
    _∙_ : Carrier → Carrier → Carrier
    e : Carrier
    --
    unitᴿ : ∀ {x : Carrier} → x ∙ e ≡ x
    unitᴸ : ∀ {x : Carrier} → e ∙ x ≡ x
    assoc : ∀ {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record LeftModule {M : Monoid} : Set (suc zero) where
  open module M = Monoid M
  field
    S : Set 
    _⋆_ : M.Carrier → S → S
    act₁ : ∀ {s : S} → M.e ⋆ s ≡ s
    act∙ : ∀ {x y : M.Carrier} {s : S} → (M._∙_ x y) ⋆ s ≡ x ⋆ (y ⋆ s)


record rotThirteenoid : Set (suc zero) where
  field
    E A : Set
    d : A × E → E 
    s : A × E → A 
    m : E × E → E
    mistero : ∀ {a e e'} → d (a , m (e , e')) ≡ m (d (a , e) , d (s (a , e) , e'))

  d∞ : List A × E → E 
  d∞ ([] , e) = e
  d∞ (x ∷ xs , e) = d (x , d∞ (xs , e))

  mistero2 : ∀ {a1 a2 : A} {e e' : E} → d∞ (a1 ∷ a2 ∷ [] , m (e , e')) ≡ {! d (a1 , d (a2 , m (e , e'))) !}
  mistero2 {a1} {a2} {e} {e'} = 
    begin d (a1 , d∞ (a2 ∷ [] , m (e , e'))) 
            ≡⟨ cong (λ t → d (a1 , t)) mistero ⟩
          d (a1 , m (d (a2 , e) , d (s (a2 , e) , e'))) 
            ≡⟨ mistero ⟩
          m (d (a1 , d (a2 , e)) , d (s (a1 , d (a2 , e)) , d (s (a2 , e) , e'))) 
            ∎
