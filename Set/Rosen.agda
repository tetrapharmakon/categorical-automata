module Set.Rosen where

open import Set.Automata
open import Data.Sum
open import Data.Product
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)

private
  variable
    A B C D E F I O : Set

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

jop : {X : MR A B} {Y : MR C D} {Z : MR E F} (h : MR⇒ X Y) (k : MR⇒ Y Z) → MR⇒ X Z
jop {X = X} {Y = Y} {Z = Z} h k = 
  let module X = MR X
      module Y = MR Y
      module Z = MR Z 
      module h = MR⇒ h 
      module k = MR⇒ k in record 
    { u = k.u ∘ h.u 
    ; v = k.v ∘ h.v 
    ; comp-f = λ { a → trans (k.comp-f (h.u a)) (cong k.v (h.comp-f a)) } 
    ; comp-ϕ = λ { b a → trans (cong k.v (h.comp-ϕ b a)) (k.comp-ϕ (h.v b) (h.u a)) } 
    } 

⟦_⟧ : MR I O → Mealy I O 
⟦_⟧ {I} {O} M = record 
  { E = I → O 
  ; d = λ { (i , f) i' → M.ϕ (f i) i' } 
  ; s = λ { (i , f) → f i } 
  } where module M = MR M

pollo : (y : MR B C) → (x : MR A B) → Mealy.d (⟦ y ⟧ ⋄ ⟦ x ⟧) 
  ≡ λ { (a , (u , t)) → (λ i' → ϕ x (u a) i') , λ i' → ϕ y (t (Mealy.s ⟦ x ⟧ (a , u))) i' }
pollo y x = refl

papero : (y : MR B C) → (x : MR A B) → Mealy.s (⟦ y ⟧ ⋄ ⟦ x ⟧) 
  ≡ λ { (a , (u , t)) → t (Mealy.s ⟦ x ⟧ (a , u)) }
papero y x = refl

--cecck-morphisms : {X : MR A B} {Y : MR C D} (h : MR⇒ X Y) → Mealy⇒ ⟦ X ⟧ ⟦ Y ⟧
--cecck-morphisms = ?
--
--
record StortoMealy (I : Set) (O : Set) : Set₁ where
  eta-equality
  field
    S : Set
    b : O → S
    s : I × S → O


μ : (x : StortoMealy A B) → Mealy A B
μ x = record 
  { E = x.S 
  ; d = x.b ∘ x.s 
  ; s = x.s 
  } where module x = StortoMealy x


dcompo-test : (x : StortoMealy A B) (y : StortoMealy B C) → Mealy.d ((μ y) ⋄ (μ x)) 
  ≡ λ { (a , (s , s')) → Mealy.d (μ x) (a , s) , Mealy.d (μ y) (Mealy.s (μ x) (a , s) , s') }
dcompo-test x y = refl


scompo-test : (x : StortoMealy A B) (y : StortoMealy B C) → Mealy.s ((μ y) ⋄ (μ x)) 
  ≡ λ { (a , (s , s')) → StortoMealy.s y (Mealy.s (μ x) (a , s) , s') }
scompo-test x y = refl

