module Set.CrossedModules where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Monoid (Carrier : Set) : Set (suc zero) where
  field
    _∙_ : Carrier → Carrier → Carrier
    e : Carrier
    --
    unitᴿ : ∀ {x : Carrier} → x ∙ e ≡ x
    unitᴸ : ∀ {x : Carrier} → e ∙ x ≡ x
    assoc : ∀ {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record IsMonoid A : Set (suc zero) where
  field
    isMonoid : Monoid A

open IsMonoid

--record LeftModule {M : Monoid} : Set (suc zero) where
  --open module M = Monoid M
  --field
    --S : Set 
    --_⋆_ : M.Carrier → S → S
    --act₁ : ∀ {s : S} → M.e ⋆ s ≡ s
    --act∙ : ∀ {x y : M.Carrier} {s : S} → (M._∙_ x y) ⋆ s ≡ x ⋆ (y ⋆ s)


record rotThirteenoid : Set (suc zero) where
  field
    E A : Set
    _⊗_ : A → E → E 
    _⊙_ : A → E → A 
    monE : IsMonoid E
  _∙_ = Monoid._∙_ (isMonoid monE)
  field
    mistero : ∀ {a e e'} → a ⊗ (e ∙ e') ≡ ((a ⊗ e) ∙ ((a ⊙ e) ⊗ e'))

  e0 = Monoid.e (isMonoid monE)

  d∞ : List A → E → E 
  d∞ [] e = e
  d∞ (x ∷ xs) e = x ⊗ (d∞ xs e)

  s∞ : List A → E → List A 
  s∞ [] e = []
  s∞ (a ∷ as) e = (a ⊙ (d∞ as e)) ∷ (s∞ as e)

  _⊗⋆_ : List A → E → E 
  as ⊗⋆ e = d∞ as e

  _⊙⋆_ : List A → E → List A 
  as ⊙⋆ e = s∞ as e

  _∙⋆_ : E → E → E 
  e ∙⋆ e' = e ∙ e'

  A1 : ∀ {k h h'} → k ⊗⋆ (h ∙ h') ≡ ((k ⊗⋆ h) ∙ ((k ⊙⋆ h) ⊗⋆ h'))
  A1 {[]} {h} {h'} = refl
  A1 {x ∷ xs} {h} {h'} = 
    begin x ⊗ d∞ xs (h ∙ h') 
            ≡⟨ cong (λ t → x ⊗ t) (A1 {xs} {h} {h'}) ⟩
          x ⊗ (d∞ xs h ∙ d∞ (s∞ xs h) h') 
            ≡⟨ mistero ⟩
          ((x ∷ xs) ⊗⋆ h) ∙ (((x ∷ xs) ⊙⋆ h) ⊗⋆ h')
            ∎

  A2 : ∀ {k k' h} → (k ++ k') ⊙⋆ h ≡ (k ⊙⋆ (k' ⊗⋆ h)) ++ (k' ⊙⋆ h)
  A2 {[]} {[]} {h} = refl
  A2 {[]} {x ∷ k'} {h} = refl
  A2 {x ∷ k} {[]} {h} =
    begin (x ⊙ d∞ (k ++ []) h) ∷ s∞ (k ++ []) h 
            ≡⟨ cong (λ t → (x ⊙ d∞ t h) ∷ s∞ t h) (++-identityʳ k) ⟩
          (x ⊙ d∞ k ([] ⊗⋆ h)) ∷ s∞ k ([] ⊗⋆ h) 
            ≡⟨ sym (++-identityʳ _) ⟩
          (x ⊙ d∞ k ([] ⊗⋆ h)) ∷ s∞ k ([] ⊗⋆ h) ++ ([] ⊙⋆ h)
            ∎
  A2 {x ∷ xs} {y ∷ ys} {h} =
    begin (x ⊙ d∞ (xs ++ y ∷ ys) h) ∷ s∞ (xs ++ y ∷ ys) h 
            ≡⟨ cong (λ t → (x ⊙ d∞ (xs ++ y ∷ ys) h) ∷ t) (A2 {xs} {y ∷ ys} {h}) ⟩
          (x ⊙ d∞ (xs ++ y ∷ ys) h) ∷ s∞ xs (y ⊗ d∞ ys h) ++ (y ⊙ d∞ ys h) ∷ s∞ ys h 
            ≡⟨ cong (λ t → t ∷ (s∞ xs (y ⊗ d∞ ys h) ++ (y ⊙ d∞ ys h) ∷ s∞ ys h)) (cong (λ r → x ⊙ r) {! !}) ⟩
          (x ⊙ d∞ xs ((y ∷ ys) ⊗⋆ h)) ∷ s∞ xs ((y ∷ ys) ⊗⋆ h) ++ ((y ∷ ys) ⊙⋆ h)
            ∎
  BiCrossed : Monoid (E × List A)
  BiCrossed = record 
    { _∙_ = λ { (x , as) (x' , bs) → (M._∙_ x (as ⊗⋆ x')) , (as ⊙⋆ x') ++ bs }
    ; e = e0 , [] 
    ; unitᴿ = λ { {x , as} → 
        begin {! !} 
            ≡⟨ cong (λ t → (M._∙_ x (d∞ as e)) , t) (++-identityʳ _) ⟩
          {! !}
            ≡⟨ {! !} ⟩
          {! !} 
            ∎ }
    ; unitᴸ = λ { {x , as} → cong (λ t → t , as) unitᴸ }
    ; assoc = λ { {x , as} {y , bs} {z , cs} → {! !} }
    } where open module M = Monoid (isMonoid monE)
  --mistero2 : ∀ {a1 a2 : A} {e e' : E} → d∞ (a1 ∷ a2 ∷ [] , m (e , e')) ≡ {! d (a1 , d (a2 , m (e , e'))) !}
  --mistero2 {a1} {a2} {e} {e'} = 
    --begin d (a1 , d∞ (a2 ∷ [] , m (e , e'))) 
            --≡⟨ cong (λ t → d (a1 , t)) mistero ⟩
          --d (a1 , m (d (a2 , e) , d (s (a2 , e) , e'))) 
            --≡⟨ mistero ⟩
          --m (d (a1 , d (a2 , e)) , d (s (a1 , d (a2 , e)) , d (s (a2 , e) , e'))) 
            --∎
