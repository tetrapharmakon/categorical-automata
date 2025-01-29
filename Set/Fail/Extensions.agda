{-# OPTIONS --allow-unsolved-metas #-}
module Set.Fail.Extensions where

open import Set.Automata
open import Set.LimitAutomata
open import Set.DoubleCategory
open import Set.Functors
open import Level
open import Function

open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

private
  variable
    X Y Z A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B

record _isRan_along_ (Ran : Mealy B C) (G : Mealy A C) (F : Mealy A B) : Set (suc zero) where
  field
    ρ : Cell id id (Ran ⋄ F) G
    universal : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) →
      Cell id id H Ran
    commute : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) →
      Cell≡ ξ ((idCell F ⊙ₕ universal H ξ) ⊙ᵥ ρ)
    unique : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) (c : Cell id id H Ran) (pc : Cell≡ ξ ((idCell F ⊙ₕ c) ⊙ᵥ ρ)) →
      Cell≡ c (universal H ξ)

Ran_⟨_⟩ : (F : Mealy A B) (G : Mealy A C) → (a : A) → (e : Mealy.E F) → Mealy B C
Ran_⟨_⟩ F G a e = record
  { E = (F.E → G.E)
  ; d = λ { (b , u) → λ { x → u x } }
  ; s = λ { (b , u) → G.s (a , u e) } -- G.s ({! !} , u {! !}) }
  } where module F = Mealy F
          module G = Mealy G

module _ {F : Mealy A B} {G : Mealy A C} {R : Mealy B C} where

  module F = Mealy F
  module G = Mealy G
  module R = Mealy R


  fleshoutRan : (H : Mealy B C) → (ρ : F.E → R.E → G.E)
    → R isRan G along F
  fleshoutRan H ρ = record
    { ρ = record
      { α = λ { (f , r) → ρ f r } -- ρ : F.E × R.E → G.E
      ; com-s = λ { {a} {f , r} → {! !} } -- G.s (a , ρ f r) ≡ R.s (F.s (a , f) , r)
      ; com-d = λ { {a} {f , r} → {! !} } -- G.d (a , ρ f r) ≡ ρ (F.d (a , f)) (R.d (F.s (a , f) , r))
      }
    ; universal = λ { H ξ → let module H = Mealy H
                                module ξ = Cell ξ in record
      { α = {!ξ.com-s !} -- Goal: ν : H.E → R.E
      ; com-s = λ { {b} {h} → {! !} } -- Goal: R.s (b , ν h) ≡ H.s (b , h)
      ; com-d = λ { {b} {h} → {! !} } -- Goal: R.d (b , ν h) ≡ ν (H.d (b , h))
      } }
    ; commute = λ { H ξ → let module ξ = Cell ξ in record { eq = λ { {f , h} → {! !} } } } -- Goal: ξ.α (f , h) ≡ ρ f (ν h)
    ; unique = λ { H ξ c pc → let module ξ = Cell ξ
                                  module c = Cell c
      in record { eq = λ { {h} → {! !} } } } -- Goal: c.α h ≡ ν h
     }


  {-
  A -------------F-----------> B
  |                            |
  |                            |
  |                            |
  |                            |
  A -----G----> C ....L......> B
  -}

record _isLan_along_ (Lan : Mealy C B) (F : Mealy A B) (G : Mealy A C) : Set (suc zero) where
  field
    η : Cell id id F (Lan ⋄ G)
    universal : ∀ (H : Mealy C B) (ξ : Cell id id F (H ⋄ G)) → Cell id id Lan H
    commute : ∀ (H : Mealy C B) (ξ : Cell id id F (H ⋄ G)) → Cell≡ ξ (η ⊙ᵥ (idCell G ⊙ₕ universal H ξ)) -- ((idCell F ⊙ₕ universal H ξ) ⊙ᵥ ρ)
    unique : ∀ (H : Mealy C B) (ξ : Cell id id F (H ⋄ G)) (c : Cell id id Lan H) (pc : Cell≡ ξ (η ⊙ᵥ (idCell G ⊙ₕ universal H ξ))) → Cell≡ c (universal H ξ)


module _ {X : Mealy A C} {Y : Mealy A B} {L : Mealy B C} where

  module X = Mealy X
  module Y = Mealy Y
  module L = Mealy L

  fleshoutLan : (η : X.E → Y.E × L.E)
       → (gimmeNu : (H : Mealy B C) (ξ : Cell id id X (H ⋄ Y)) → Cell id id L H)
       → L isLan X along Y
  fleshoutLan η gimmeNu = record
    { η = record
      { α = η
      ; com-s = λ { {a} {x} → {! !} } -- L.s (Y.s (a , η₁ x) , η₂ x) ≡ X.s (a , x)
      ; com-d = λ { {a} {x} → {! !} } -- (Y.d (a , η₁ x) , L.d (Y.s (a , η₁ x) , η₂ x)) ≡ η (X.d (a , x))
      }
    ; universal = λ { H ξ → let module H = Mealy H
                                module ξ = Cell ξ in record
      { α = Cell.α (gimmeNu H ξ) -- nu
      ; com-s = λ { {b} {h} → {! !} } -- Goal: H.s (b , nu h) ≡ L.s (b , h)
      ; com-d = λ { {b} {h} → {!  !} } -- Goal: H.d (b , nu h) ≡ nu (L.d (b , h))
      } }
    ; commute = λ { H ξ → record { eq = λ { {x} → {!  !} } } } -- α ξ x ≡ (η₁ x , Cell.α (nu H ξ) η₁ x)
    ; unique = λ { H ξ c pc → {!  !} } --
    }


record _isRift_along_ (R : Mealy A B) (G : Mealy A X) (F : Mealy B X) : Set (suc zero) where
  field
    ε : Cell id id (F ⋄ R) G
    universal : ∀ (H : Mealy A B) (ξ : Cell id id (F ⋄ H) G) → Cell id id H R
    commute : ∀ (H : Mealy A B) (ξ : Cell id id (F ⋄ H) G) → Cell≡ ξ ((universal H ξ ⊙ₕ idCell F) ⊙ᵥ ε)
    unique : ∀ (H : Mealy A B) (ξ : Cell id id (F ⋄ H) G) (c : Cell id id H R) (pc : Cell≡ ξ ((universal H ξ ⊙ₕ idCell F) ⊙ᵥ ε)) →
      Cell≡ c (universal H ξ)

module _ {R : Mealy A B} {G : Mealy A X} {F : Mealy B X} where
  --module F = Mealy F
  --module G = Mealy G
  --module R = Mealy R

  candidateRift : Mealy A B
  candidateRift = record
    { E = F.E → G.E
    ; d = λ { (a , u) f → u f }
    ; s = λ { (a , u) → {!  !} } }

  fleshoutRift : (ε : R.E × F.E → G.E) → R isRift G along F
  fleshoutRift ε = record
    { ε = record
      { α = ε
--Goal: R.E × F.E → G.E
      ; com-s = λ { {a} {r , f} → {!  !} }
--Goal: G.s (a , ε (r , f)) ≡ F.s (R.s (a , r) , f)
      ; com-d = λ { {a} {r , f} → {!  !} } }
--Goal: G.d (a , ε (r , f)) ≡ ε (R.d (a , r) , F.d (R.s (a , r) , f))
    ; universal = {!  !}
    ; commute = {!  !}
    ; unique = {!  !} }
