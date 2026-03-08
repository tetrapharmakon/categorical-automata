module MRS where

open import Level using (Level; _⊔_; zero; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Axiom.Extensionality.Propositional using (extensionality)

-- A record matching your Haskell datatype:
record MRS {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    f   : A → B
    phi : B → A → B

open MRS public

-- Your l, r, k:
l : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → MRS A B
l f₀ = record
  { f   = f₀
  ; phi = λ x a → x
  }

r : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → MRS A B
r f₀ = record
  { f   = f₀
  ; phi = λ x → f₀
  }

k : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → MRS A B → A → B
k x a = phi x (f x a) a

-- Compose like in Haskell:
kl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → A → B
kl = k ∘ l

kr : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → A → B
kr = k ∘ r

-- Proofs: k ∘ l = id and k ∘ r = id (as function equality).
-- We use extensionality twice: once over f, once over a.
k∘l≡id : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (k ∘ l) ≡ (λ (f₀ : A → B) → f₀)
k∘l≡id = ?

k∘r≡id : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (k ∘ r) ≡ (λ (f₀ : A → B) → f₀)
k∘r≡id = ?