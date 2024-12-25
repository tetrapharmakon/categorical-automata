{-# OPTIONS --allow-unsolved-metas #-}
module Set.CrossedModules where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Set.Automata

private
  variable
    A B C X Y Z M₀ : Set

record IsMonoid (Carrier : Set) : Set (suc zero) where
  field
    _∙_ : Carrier → Carrier → Carrier
    u : Carrier
    --
    unitᴿ : ∀ {x : Carrier} → x ∙ u ≡ x
    unitᴸ : ∀ {x : Carrier} → u ∙ x ≡ x
    assoc : ∀ {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record Monoid : Set (suc zero) where
  field
    Carrier : Set
    isMonoid : IsMonoid Carrier

record _actsOnᴸ_ (M : IsMonoid M₀) (A : Set) : Set (suc zero) where
  open module M = IsMonoid M
  field
    act : M₀ → A → A
    unit : ∀ {a} → act u a ≡ a
    assoc : ∀ {a x y} → act x (act y a) ≡ act (x ∙ y) a

record _actsOnᴿ_ (M : IsMonoid M₀) (A : Set) : Set (suc zero) where
  open module M = IsMonoid M
  field
    act : A → M₀ → A
    unit : ∀ {a} → act a u ≡ a
    assoc : ∀ {a x y} → act (act a x) y ≡ act a (x ∙ y)

--record LeftModule {M : IsMonoid} : Set (suc zero) where
  --open module M = IsMonoid M
  --field
    --S : Set
    --_⋆_ : M.Carrier → S → S
    --act₁ : ∀ {s : S} → M.e ⋆ s ≡ s
    --act∙ : ∀ {x y : M.Carrier} {s : S} → (_∙_ x y) ⋆ s ≡ x ⋆ (y ⋆ s)

record MonadInMealy : Set (suc zero) where
  field
    E : Set
    _⊗_ : A → E → E
    _⊙_ : A → E → A
    monE : IsMonoid E

  open IsMonoid monE

  field
    mistero : ∀ {a e e'} → a ⊗ (e ∙ e') ≡ ((a ⊗ e) ∙ ((a ⊙ e) ⊗ e'))

  field
    fix : ∀ {a} → a ⊗ u ≡ u

  d∞ : List A → E → E
  d∞ [] e = e
  d∞ (x ∷ xs) e = x ⊗ (d∞ xs e)

  s∞ : List A → E → List A
  s∞ [] e = []
  s∞ (a ∷ as) e = (a ⊙ (d∞ as e)) ∷ (s∞ as e)

  lemmuzzo : ∀ {as} → d∞ as u ≡ u
  lemmuzzo {[]} = refl
  lemmuzzo {x ∷ as} = trans (cong (λ t → x ⊗ t) lemmuzzo) fix

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

  BiCrossed : IsMonoid (E × List A)
  BiCrossed = record
    { _∙_ = λ { (x , as) (x' , bs) → (_∙_ x (as ⊗⋆ x')) , (as ⊙⋆ x') ++ bs }
    ; u = u , []
    ; unitᴿ = λ { {x , as} →
        begin
          (x ∙ (as ⊗⋆ u)) , (as ⊙⋆ u) ++ []
            ≡⟨ cong (λ t → (_∙_ x (d∞ as u)) , t) (++-identityʳ _) ⟩
          (x ∙ d∞ _ u) , s∞ as u
            ≡⟨ cong₂ _,_ (trans (cong (λ t → x ∙ t) lemmuzzo) unitᴿ) {! !} ⟩
            -- questo segue da una eq. di Mealy
          x , as
            ∎ }
    ; unitᴸ = λ { {x , as} → cong (λ t → t , as) unitᴸ }
    ; assoc = λ { {x , as} {y , bs} {z , cs} → {! !} }
    }

  theorem : {U : Mealy X A} → BiCrossed actsOnᴸ (Mealy.E U)
  theorem {U = U} = record
    { act = λ { (m , as) x → {!  (as ⊗⋆ m) !} } -- e ∙ d(as , x) ?
    ; unit = {! !}
    ; assoc = {! !}
    } where module U = Mealy U

open MonadInMealy


record miracolo {G₀ H₀ : Set} : Set (suc zero) where
  field
    Carrier : Set
    G : IsMonoid G₀
    H : IsMonoid H₀
  module G = IsMonoid G
  module H = IsMonoid H
  field
    ◁ : G actsOnᴸ X
    ▷ : H actsOnᴸ X
