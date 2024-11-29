{-# OPTIONS --allow-unsolved-metas #-} 
module Set.Monads where

open import Set.Automata
open import Set.LimitAutomata
open import Set.Functors
open import Set.DoubleCategory
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

record DoubleMonad {A : Set} : Set (suc zero) where 
  field
    M : Mealy A A
    η : Cell id id idMealy M
    μ : Cell id id (M ⋄ M) M
    unitᴸ : Cell≡ (unitorᴸ M ⊙ᵥ ((η ⊙ₕ idCell M) ⊙ᵥ μ)) (idCell M)
    unitᴿ : Cell≡ (unitorᴿ⁻¹ M ⊙ᵥ ((idCell M ⊙ₕ η) ⊙ᵥ μ)) (idCell M)
    μ-assoc : Cell≡ ((idCell M ⊙ₕ μ) ⊙ᵥ μ) (assoc⁻¹ ⊙ᵥ ((μ ⊙ₕ idCell M) ⊙ᵥ μ))

-- fleshout di una monade
esempio : {A : Set} 
  (M : Mealy A A) 
  (e₀ : ⊤ → Mealy.E M) 
  (m : Mealy.E M × Mealy.E M → Mealy.E M) → DoubleMonad {A}
esempio M e₀ m = record 
  { M = M -- M : A × E --⟨d,s⟩-→ E × A; 
    -- d : A × E → E | action of List A on E
    -- s : A × E → A | action of E on A 
  ; η = record 
    { α = e₀ -- ⊤ → E
    ; com-s = {!  !} 
    -- ∀ {a : A} → s (a , e) ≡ a
    -- a ◁ e ≡ a
    ; com-d = {! !} 
    -- ∀ {a : A} → d (a , e) ≡ e
    -- the identity of (E, ∙) is a fixpoint for d
    } 
  ; μ = record 
    { α = m 
    ; com-s = λ { {a} {e , e'} → {! !} }
    -- s (a , m (e , e')) ≡ s (s (a , e) , e')
    -- s (a , e ∙ e') ≡ s (s (a , e) , e' )
    -- a ◁ (e ∙ e') ≡ (a ◁ e) ◁ e'
    ; com-d = λ { {a} {e , e'} → {! !} }
    -- d (a , m (e , e')) ≡ m (d (a , e) , d (s (a , e) , e'))
    -- a ⊛ (e ∙ e') ≡ (a ⊛ e) ∙ ((a ◁ e) ⊛ e')
    } 
  ; unitᴸ = record { eq = {! !} } -- m (e , x) ≡ x
  ; unitᴿ = record { eq = {! !} } -- m (x , e) ≡ x
  ; μ-assoc = record { eq = λ { {e , e' , e''} → {! !} } } 
    -- PROBABLY m (e , m (e' , e'')) ≡ m (m(e , e') , e'')
  } where module M = Mealy M


{-
* ------- M ------- * 
|                   |
|         σ         |
|                   |
* ---M--- * ---M--- *
|         |         |
|         |         |
|         |         |
* ------- * ------- *
-}

record DoubleComonad {A : Set} : Set (suc zero) where 
  field
    M : Mealy A A
    ε : Cell id id M idMealy
    σ : Cell id id M (M ⋄ M)
    counitᴸ : Cell≡ (σ ⊙ᵥ ((idCell M ⊙ₕ ε) ⊙ᵥ unitorᴿ M)) (idCell M)
    counitᴿ : Cell≡ (σ ⊙ᵥ ((ε ⊙ₕ idCell M) ⊙ᵥ unitorᴸ⁻¹ M)) (idCell M)
    σ-coassoc : Cell≡ (σ ⊙ᵥ (idCell M ⊙ₕ σ)) ((σ ⊙ᵥ (σ ⊙ₕ idCell M)) ⊙ᵥ assoc)


candidateComonad : {X : Set} → Mealy A A
candidateComonad {X = X} = record 
  { E = X
  ; d = {! !} -- can be any action
  ; s = proj₁ 
  }

-- prolly only the canonical comonad structure?
fleshoutComonad : {A} → 
  DoubleComonad {A}
fleshoutComonad = record 
  { M = candidateComonad 
  ; ε = record 
    { α = λ { x → tt } 
    ; com-s = refl -- solo se s è la proiezione!
    ; com-d = refl 
    } 
  ; σ = record 
    { α = λ { x → x , x } 
    ; com-s = λ { {a} {e} → refl }
-- M.s (M.s (a , proj₁ (σ e)) , proj₂ (σ e)) ≡ M.s (a , e)
    ; com-d = λ { {a} {e} → refl }
-- (M.d (a , proj₁ (σ e)) , M.d (M.s (a , proj₁ (σ e)) , proj₂ (σ e))) ≡ σ (M.d (a , e))
    } 
  ; counitᴸ = record { eq = refl } 
  ; counitᴿ = record { eq = refl } 
  ; σ-coassoc = record { eq = λ { {x} → refl } }
  } 
