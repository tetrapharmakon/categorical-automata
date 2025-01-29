{-# OPTIONS --without-K --cubical-compatible #-}

module Set.DoubleCategory where

open import Set.Automata
open import Set.LimitAutomata
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
    X Y Z U V A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B
{-

A  -lh⟶  B
|        |
lv       rv
↓        ↓
A' -rh⟶  B'

α : lh.E ⟶  rh.E such that

A × E ----⟨d,s⟩⟶  E × B
  |                 |
  | lv × α          | α × rv
  |                 |
  ↓                 ↓
A' × F -⟨d',s'⟩⟶  F × B'

commutes.

-}
record Cell (lv : A → A') (rv : B → B') (lh : Mealy A B) (rh : Mealy A' B') : Set (suc zero) where
  private
    module lh = Mealy lh
    module rh = Mealy rh
  field
    α  : lh.E → rh.E
    com-s : ∀ {x y} → rh.s (lv x , α y) ≡ rv (lh.s (x , y))
    com-d : ∀ {x y} → rh.d (lv x , α y) ≡  α (lh.d (x , y))

_⊙ᵥ_ : ∀ {lh : Mealy A B} {boh : Mealy A'' B''} {rh : Mealy A' B'}
  → Cell lv' rv' lh boh
  → Cell lv rv boh rh
  → Cell (lv ∘ lv') (rv ∘ rv') lh rh
_⊙ᵥ_ {rv = rv} {lh = lh} α β =
  let module α = Cell α
      module β = Cell β in record
        { α = β.α ∘ α.α
        ; com-s = trans β.com-s (cong rv α.com-s)
        ; com-d = trans β.com-d (cong β.α α.com-d)
        }

_⊙ₕ_ : ∀ {lv : A → X} {rv : C → Z} {M' : Mealy A B} {M : Mealy B C} {N' : Mealy X Y} {N : Mealy Y Z} {boh : B → Y}
  → Cell lv boh M' N'
  → Cell boh rv M N
  → Cell lv rv (M ⋄ M') (N ⋄ N')
_⊙ₕ_ {M' = M'} {M = M} {N' = N'} {N = N} μ ν =
  let module μ = Cell μ
      module ν = Cell ν
      module M = Mealy M
      module N = Mealy N
      module M' = Mealy M'
      module N' = Mealy N' in
  record
    { α = map μ.α ν.α
    ; com-s = λ { {y = (z , w)} →
        trans (cong (λ t → N.s (t , ν.α w)) μ.com-s) ν.com-s
      }
    ; com-d = λ { {y = (z , w)} →
        cong₂ _,_ μ.com-d (trans (cong (λ t → N.d (t , ν.α w)) μ.com-s) ν.com-d)
      }
    }

record Cell≡ {lh : Mealy A B} {rh : Mealy A' B'} (C C' : Cell lv rv lh rh) : Set (suc zero) where
  private
    module C  = Cell C
    module C' = Cell C'
  field
    eq : ∀ {x} → C.α x ≡ C'.α x

idH : ∀ (h : X → Y) → Cell h h idMealy idMealy
idH h = record
  { α = id
  ; com-s = refl
  ; com-d = refl
  }

idCell : ∀ (M : Mealy X Y) → Cell id id M M
idCell M = record
  { α = id
  ; com-s = refl
  ; com-d = refl
  }

unitorᴸ : ∀ (M : Mealy X Y) → Cell id id M (M ⋄ idMealy)
unitorᴸ M = record
  { α = λ { x → tt , x }
  ; com-s = refl
  ; com-d = refl
  }

unitorᴿ : ∀ (M : Mealy X Y) → Cell id id (idMealy ⋄ M) M
unitorᴿ M = record
  { α = λ { (e , _) → e }
  ; com-s = refl
  ; com-d = refl
  }

unitorᴸ⁻¹ : ∀ (M : Mealy X Y) → Cell id id (M ⋄ idMealy) M
unitorᴸ⁻¹ M = record
  { α = λ { (_ , e) → e }
  ; com-s = refl
  ; com-d = refl
  }

unitorᴿ⁻¹ : ∀ (M : Mealy X Y) → Cell id id M (idMealy ⋄ M)
unitorᴿ⁻¹ M = record
  { α = λ { x → x , tt }
  ; com-s = refl
  ; com-d = refl
  }

assoc : ∀ (P : Mealy Z A) (N : Mealy Y Z) (M : Mealy X Y) → Cell id id (P ⋄ (N ⋄ M)) ((P ⋄ N) ⋄ M)
assoc P N M = record
  { α = λ { ((e , f) , p) → e , f , p }
  ; com-s = refl
  ; com-d = refl
  } where module M = Mealy M
          module N = Mealy N
          module P = Mealy P

assoc⁻¹ : ∀ (P : Mealy Z A) (N : Mealy Y Z) (M : Mealy X Y) → Cell id id ((P ⋄ N) ⋄ M) (P ⋄ (N ⋄ M))
assoc⁻¹ P N M = record
  { α = λ { (e , f , p) → (e , f) , p }
  ; com-s = refl
  ; com-d = refl
  } where module M = Mealy M
          module N = Mealy N
          module P = Mealy P
