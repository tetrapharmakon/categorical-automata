{-# OPTIONS --allow-unsolved-metas #-}
module Set.Limits where

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

open import Set.Equality

private
  variable
    X Y Z U V A B C A' B' A'' B'' : Set
    lv rv lv' rv' : A → B

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

record Companion {A B} (f : A → B) : Set (suc zero) where
  field
    comp : Mealy A B -- the loose arrow
    Λ : Cell f id comp idMealy -- the first cell filling the square
    Ξ : Cell id f idMealy comp -- the second cell filling the square
  module Λ = Cell Λ
  module Ξ = Cell Ξ
  field
    zig : Cell≡ (idH f) (Ξ ⊙ᵥ Λ)
    zag : Cell≡ (unitorᴸ comp ⊙ᵥ ((Ξ ⊙ₕ Λ) ⊙ᵥ unitorᴿ comp)) (idCell comp)

record Conjoint {A B} (f : A → B) : Set (suc zero) where
  field
    conj : Mealy B A -- the loose arrow
    Λ : Cell f id idMealy conj -- the first cell filling the square
    Ξ : Cell id f conj idMealy -- the second cell filling the square
  module Λ = Cell Λ
  module Ξ = Cell Ξ
  field
    zig : Cell≡ (idH f) (Λ ⊙ᵥ Ξ)
    zag : Cell≡ (unitorᴿ⁻¹ conj ⊙ᵥ ((Ξ ⊙ₕ Λ) ⊙ᵥ unitorᴸ⁻¹ conj)) (idCell conj)

_ₒ : (f : A → B) → Companion f
f ₒ = record
  { comp = record
    { E = ⊤
    ; d = λ { x → tt }
    ; s = λ { (a , _) → f a }
    }
  ; Λ = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; Ξ = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; zig = record { eq = refl }
  ; zag = record { eq = refl }
  }

record DoubleTerminal : Set (suc zero) where
  field
    ⊤⊤ : Set
    universal₁ : ∀ {X Y} (M : Mealy X Y) → (X → ⊤⊤) × (Y → ⊤⊤)
    universal₂ : ∀ {X Y} (M : Mealy X Y) → Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) M idMealy
    unique : ∀ {X Y} {M : Mealy X Y} {c : Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) M idMealy} → Cell≡ c (universal₂ M)

record DoubleProduct (A B : Set) : Set (suc zero) where
  field
    prod : Set
    p₁ : prod → A
    p₂ : prod → B
    π₁ : Cell p₁ p₁ idMealy idMealy
    π₂ : Cell p₂ p₂ idMealy idMealy
    universal₁ : ∀ {u : Mealy X Y} {a : X → A} {a' : Y → A} {b : X → B} {b' : Y → B} →
      (ξ₁ : Cell a a' u idMealy) (ξ₂ : Cell b b' u idMealy) →
      (X → prod) × (Y → prod)
    universal₂ : ∀ {u : Mealy X Y} {a : X → A} {a' : Y → A} {b : X → B} {b' : Y → B} →
      (ξ₁ : Cell a a' u idMealy) (ξ₂ : Cell b b' u idMealy) →
      (Cell (proj₁ (universal₁ ξ₁ ξ₂)) (proj₂ (universal₁ ξ₁ ξ₂)) u idMealy)
    fst-commute₁ : ∀ {u : Mealy X Y} {a : X → A} {a' : Y → A} {b : X → B} {b' : Y → B} →
      (ξ₁ : Cell a a' u idMealy) (ξ₂ : Cell b b' u idMealy) →
      (p₁ ∘ proj₁ (universal₁ ξ₁ ξ₂) ≡ a) × (p₁ ∘ proj₂ (universal₁ ξ₁ ξ₂) ≡ a')
    snd-commute₁ : ∀ {u : Mealy X Y} {a : X → A} {a' : Y → A} {b : X → B} {b' : Y → B} →
      (ξ₁ : Cell a a' u idMealy) (ξ₂ : Cell b b' u idMealy) →
      (p₂ ∘ proj₁ (universal₁ ξ₁ ξ₂) ≡ b) × (p₂ ∘ proj₂ (universal₁ ξ₁ ξ₂) ≡ b')
    fst-commute₂ : ∀ {u : Mealy X Y}  {a : X → A} {a' : Y → A} {b : X → B} {b' : Y → B} →
      (ξ₁ : Cell a a' u idMealy) (ξ₂ : Cell b b' u idMealy) →
      (Cell≡ ξ₁ (subst₂ (λ Q R → Cell Q R u idMealy) (proj₁ (fst-commute₁ ξ₁ ξ₂)) (proj₂ (fst-commute₁ ξ₁ ξ₂)) (universal₂ ξ₁ ξ₂ ⊙ᵥ π₁)))
    snd-commute₂ : ∀ {u : Mealy X Y} {a : X → A} {a' : Y → A} {b : X → B} {b' : Y → B} →
      (ξ₁ : Cell a a' u idMealy) (ξ₂ : Cell b b' u idMealy) →
      (Cell≡ ξ₂ (subst₂ (λ Q R → Cell Q R u idMealy) (proj₁ (snd-commute₁ ξ₁ ξ₂)) (proj₂ (snd-commute₁ ξ₁ ξ₂)) (universal₂ ξ₁ ξ₂ ⊙ᵥ π₂)))

record DoublePB (f : X → A) (g : Y → A) : Set (suc zero) where
  field
    pb : Set
    pX : pb → X
    πX : Cell pX pX idMealy idMealy
    pY : pb → Y
    πY : Cell pY pY idMealy idMealy
    commute : ∀ {t : pb} → f (pX t) ≡ g (pY t)
    universal₁ :
      ∀ {u : Mealy U V}
        {x : U → X}
        {x' : V → X}
        {y : U → Y}
        {y' : V → Y}
        (c : ∀ {t} → f (x t) ≡ g (y t))
        (c' : ∀ {t} → f (x' t) ≡ g (y' t))
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) →
          (U → pb) × (V → pb)
    universal₂ :
      ∀ {u : Mealy U V}
        {x : U → X}
        {x' : V → X}
        {y : U → Y}
        {y' : V → Y}
        (c : ∀ {t} → f (x t) ≡ g (y t))
        (c' : ∀ {t} → f (x' t) ≡ g (y' t))
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) →
          (Cell (proj₁ (universal₁ c c' ξ₁ ξ₂)) (proj₂ (universal₁ c c' ξ₁ ξ₂)) u idMealy)
    fst-commute₁ :
      ∀ {u : Mealy U V}
        {x : U → X}
        {x' : V → X}
        {y : U → Y}
        {y' : V → Y}
        {c : ∀ {t} → f (x t) ≡ g (y t) }
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) }
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) →
          (pX ∘ proj₁ (universal₁ c c' ξ₁ ξ₂) ≡ x) × (pX ∘ proj₂ (universal₁ c c' ξ₁ ξ₂) ≡ x')
    snd-commute₁ :
      ∀ {u : Mealy U V}
        {x : U → X}
        {x' : V → X}
        {y : U → Y}
        {y' : V → Y}
        {c : ∀ {t} → f (x t) ≡ g (y t) }
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) }
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) →
          (pY ∘ proj₁ (universal₁ c c' ξ₁ ξ₂) ≡ y) × (pY ∘ proj₂ (universal₁ c c' ξ₁ ξ₂) ≡ y')
    fst-commute₂ :
      ∀ {u : Mealy U V}
        {x : U → X}
        {x' : V → X}
        {y : U → Y}
        {y' : V → Y}
        {c : ∀ {t} → f (x t) ≡ g (y t) }
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) }
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) →
         Cell≡ ξ₁ (subst₂ (λ Q R → Cell Q R u idMealy)
           (proj₁ (fst-commute₁ ξ₁ ξ₂))
           (proj₂ (fst-commute₁ ξ₁ ξ₂)) (universal₂ c c' ξ₁ ξ₂ ⊙ᵥ πX))
    snd-commute₂ :
      ∀ {u : Mealy U V}
        {x : U → X}
        {x' : V → X}
        {y : U → Y}
        {y' : V → Y}
        {c : ∀ {t} → f (x t) ≡ g (y t) }
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) }
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) →
          Cell≡ ξ₂ (subst₂ (λ Q R → Cell Q R u idMealy)
           (proj₁ (snd-commute₁ ξ₁ ξ₂))
           (proj₂ (snd-commute₁ ξ₁ ξ₂)) (universal₂ c c' ξ₁ ξ₂ ⊙ᵥ πY))

existDblTerminal : DoubleTerminal
existDblTerminal = record
  { ⊤⊤ = ⊤
  ; universal₁ = λ { M → (λ { x → tt }) , λ { x → tt } }
  ; universal₂ = λ { M → record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl }
    }
  ; unique = record { eq = refl }
  }

existsDblProduct : DoubleProduct A B
existsDblProduct {A = A} {B = B} = record
  { prod = A × B
  ; p₁ = proj₁
  ; p₂ = proj₂
  ; π₁ = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; π₂ = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; universal₁ = λ { {a = a} {a' = a'} {b = b} {b' = b'} ξ₁ ξ₂ → < a , b > , < a' , b' > }
  ; universal₂ = λ { ξ₁ ξ₂ → record
    { α = λ { x → tt }
    ; com-s = λ { {x} {y} → cong₂ _,_ (Cell.com-s ξ₁) (Cell.com-s ξ₂) }
    ; com-d = refl
    } }
  ; fst-commute₁ = λ { {u = u} {a = a} {a' = a'} {b = b} {b' = b'} ξ₁ ξ₂ → refl , refl }
  ; snd-commute₁ = λ { {u = u} {a = a} {a' = a'} {b = b} {b' = b'} ξ₁ ξ₂ → refl , refl }
  ; fst-commute₂ = λ { ξ₁ ξ₂ → record { eq = refl } }
  ; snd-commute₂ = λ { ξ₁ ξ₂ → record { eq = refl } }
  }

record SubobPB (f : X → A) (g : Y → A) : Set where
  field
    fst : X
    snd : Y
    pbProperty : f fst ≡ g snd

SubobPB-ext : ∀ {X Y A : Set} {f : X → A} {g : Y → A} {fst fst′ : X} {snd snd′ : Y}
          → (d-ext : fst ≡ fst′)
          → (s-ext : snd ≡ snd′)
          → {e : f fst ≡ g snd}
          → {e' : f fst′ ≡ g snd′}
          → (let p : SubobPB f g
                 p = record { fst = fst ; snd = snd ; pbProperty = e }
                 q : SubobPB f g
                 q = record { fst = fst′ ; snd = snd′ ; pbProperty = e' } in p ≡ q)
SubobPB-ext refl refl {e = e} {e' = e'} with uip e e'
... | refl = refl

embedPB : {f : X → A} {g : Y → A} → SubobPB f g → X × Y
embedPB s = (PB.fst , PB.snd)
  where module PB = SubobPB s

existsDoublePullback : (f : X → A) → (g : Y → A) → DoublePB f g
existsDoublePullback f g = record
  { pb = SubobPB f g
  ; pX = SubobPB.fst
  ; πX = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; pY = SubobPB.snd
  ; πY = record
    { α = λ { x → tt }
    ; com-s = refl
    ; com-d = refl
    }
  ; commute = λ { {t} → SubobPB.pbProperty t }
  ; universal₁ = λ { {x = x} {x' = x'} {y = y} {y' = y'} c c' ξ₁ ξ₂ →
    (λ { t → record
      { fst = x t
      ; snd = y t
      ; pbProperty = c
      } }) ,
    (λ { t → record
      { fst = x' t
      ; snd = y' t
      ; pbProperty = c'
      } }) }
  ; universal₂ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} c c' ξ₁ ξ₂ → record
    { α = λ { t → tt }
    ; com-s = λ { {p} {q} → SubobPB-ext (Cell.com-s ξ₁) (Cell.com-s ξ₂) }
    ; com-d = refl
    } }
  ; fst-commute₁ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} ξ₁ ξ₂ →
    refl , refl }
  ; snd-commute₁ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} ξ₁ ξ₂ →
    refl , refl }
  ; fst-commute₂ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} ξ₁ ξ₂ →
    record { eq = λ { {x} → refl } } }
  ; snd-commute₂ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} ξ₁ ξ₂ →
    record { eq = λ { {x} → refl } } }
  }
