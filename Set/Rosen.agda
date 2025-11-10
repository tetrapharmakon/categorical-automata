module Set.Rosen where

open import Set.Automata
open import Data.Sum
open import Data.Product

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    A B C D I O : Set

record MR (I : Set) (O : Set) : Set₁ where
  eta-equality
  field
    f : I → O
    ϕ : O → (I → O)

open MR

record MR⇒ (X : MR A B) (Y : MR C D) : Set₁ where 
  eta-equality
  module X = MR X 
  module Y = MR Y
  field
    u : A → C 
    v : B → D 
    comp-f : ∀ a → Y.f (u a) ≡ v (X.f a)
    comp-ϕ : ∀ b → ∀ a → v (X.ϕ b a) ≡ Y.ϕ (v b) (u a)

⟦_⟧ : MR I O → Mealy I O 
⟦_⟧ {I} {O} M = record 
  { E = I → O 
  ; d = λ { (i , y) i' → M.ϕ (y i) i' } 
  ; s = λ { (i , y) → y i } 
  } where module M = MR M

pollo : (y : MR B C) → (x : MR A B) → Mealy.d (⟦ y ⟧ ⋄ ⟦ x ⟧) 
  ≡ λ { (a , (u , t)) → (λ i' → ϕ x (u a) i') , λ i' → ϕ y (t (Mealy.s ⟦ x ⟧ (a , u))) i' }
pollo y x = refl

papero : (y : MR B C) → (x : MR A B) → Mealy.s (⟦ y ⟧ ⋄ ⟦ x ⟧) 
  ≡ λ { (a , (u , t)) → t (Mealy.s ⟦ x ⟧ (a , u)) }
papero y x = refl
