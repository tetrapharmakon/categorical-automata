{-# OPTIONS --allow-unsolved-metas #-}
module Set.Fail.DoubleAdjoints where

open import Set.Automata
open import Set.LimitAutomata
open import Set.Functors
open import Level
open import Function

open import Set.DoubleCategory
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

open import Set.Fail.Conjoints

private
  variable
    X Y Z A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B

record DoubleAdjunction {A B} : Set (suc zero) where
  field
    ladj : Mealy A B
    radj : Mealy B A
    unit : Cell id id idMealy (radj ⋄ ladj)
    counit : Cell id id (ladj ⋄ radj) idMealy
    zig : Cell≡ ((unitorᴸ ladj ⊙ᵥ ((unit ⊙ₕ idCell ladj) ⊙ᵥ assoc ladj radj ladj)) ⊙ᵥ (idCell ladj ⊙ₕ counit)) (unitorᴿ⁻¹ ladj)
    zag : Cell≡ ((unitorᴿ⁻¹ radj ⊙ᵥ ((idCell radj ⊙ₕ unit) ⊙ᵥ assoc⁻¹ radj ladj radj)) ⊙ᵥ (counit ⊙ₕ idCell radj)) (unitorᴸ radj)

fleshOutAdjunction : (l : Mealy A B) → (r : Mealy B A) → (l₀ : Mealy.E l) → (r₀ : Mealy.E r) → DoubleAdjunction
fleshOutAdjunction l r l₀ r₀ = record
  { ladj = l
  ; radj = r
  ; unit = record
    { α = λ { x → (l₀ , r₀) }
    ; com-s = λ { {a} {tt} → {!!} }
    ; com-d = λ { {a} {tt} → {!!} }
    }
  ; counit = record
    { α = λ { x → tt }
    ; com-s = λ { {b} {x , y} → {! !} }
    ; com-d = λ { {b} {x , y} → refl }
    }
  ; zig = record { eq = {! !} }
  ; zag = record { eq = {! !} }
  } where module l = Mealy l
          module r = Mealy r

doubleAdjunction : {f : A → B} → (c : Conjoint f) → (z : Mealy.E (Conjoint.conj c)) → DoubleAdjunction
doubleAdjunction {f = f} c z = record
  { ladj = fₒ.comp
  ; radj = fᵒ.conj
  ; unit = record
    { α = λ { tt → tt , z }
    ; com-s = λ { {a} {tt} → {! !} } -- Mealy.s fᵒ.conj (f a , z) ≡ a
    ; com-d = λ { {a} {tt} → {! !} } -- (tt , Mealy.d fᵒ.conj (f a , z)) ≡ (tt , z)
    }
  ; counit = record
    { α = λ { x → tt }
    ; com-s = λ { {b} {z , tt} → {! !} } -- b ≡ f (Mealy.s fᵒ.conj (b , z))
    ; com-d = refl
    }
  ; zig = record { eq = refl }
  ; zag = record { eq = {! !} }
  } where module fₒ = Companion (f ₒ)
          module fᵒ = Conjoint c
