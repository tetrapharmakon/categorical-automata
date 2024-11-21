module Set.DoubleCategory where

open import Set.Automata
open import Level
open import Function


open import Data.Product using (map₁; map₂; map; <_,_>; _,_; _×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality 

record Cell {A B A' B' : Set} (lv : A → A') (rv : B → B') (lh : Mealy A B) (rh : Mealy A' B') : Set (suc zero) where
  private
    module lh = Mealy lh 
    module rh = Mealy rh
  field
    α  : lh.E → rh.E
    com-s : ∀ {x y} → rh.s (lv x , α y) ≡ rv (lh.s (x , y))
    com-d : ∀ {x y} → rh.d (lv x , α y) ≡  α (lh.d (x , y))

_⊙ᵥ_ : ∀ {A B A'' B'' A' B'} {lv rv lv' rv'} {lh : Mealy A B} {boh : Mealy A'' B''} {rh : Mealy A' B'} → Cell lv' rv' lh boh → Cell lv rv boh rh → Cell (lv ∘ lv') (rv ∘ rv') lh rh
_⊙ᵥ_ {rv = rv} {lh = lh} α β = 
  let module α = Cell α
      module β = Cell β in record 
        { α = β.α ∘ α.α 
        ; com-s = trans β.com-s (cong rv α.com-s) 
        ; com-d = trans β.com-d (cong β.α α.com-d) 
        }

record Cell≡ {A B A' B'} {lv rv} {lh : Mealy A B} {rh : Mealy A' B'} (C C' : Cell lv rv lh rh) : Set (suc zero) where
  private
    module C  = Cell C 
    module C' = Cell C'
  field
    eq : ∀ {x} → C.α x ≡ C'.α x

idH : ∀ {X Y} (h : X → Y) → Cell h h idMealy idMealy
idH h = record 
  { α = id 
  ; com-s = refl 
  ; com-d = refl 
  }

record Tabulator {X Y} (M : Mealy X Y) : Set (suc zero) where
  private
    module M = Mealy M
  field
    tab : Set
    p   : tab → X
    q   : tab → Y
    τ   : Cell p q idMealy M
    --
    universal : ∀ {U} {f : U → X} {g : U → Y} (ξ : Cell f g idMealy M) → 
      (U → tab)
    fst-commute₁ : ∀ {U} {f : U → X} {g : U → Y} (ξ : Cell f g idMealy M) → 
      p ∘ (universal ξ) ≡ f
    snd-commute₁ : ∀ {U} {f : U → X} {g : U → Y} (ξ : Cell f g idMealy M) → 
      q ∘ (universal ξ) ≡ g
    commute₂ : ∀ {U} {f : U → X} {g : U → Y} {ξ : Cell f g idMealy M} → 
      Cell≡ ξ (subst₂ (λ Q R → Cell Q R idMealy M) (fst-commute₁ ξ) (snd-commute₁ ξ) (idH (universal ξ) ⊙ᵥ τ))


