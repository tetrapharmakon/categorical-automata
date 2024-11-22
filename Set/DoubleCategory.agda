module Set.DoubleCategory where

open import Set.Automata
open import Level
open import Function


open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality 

private
  variable
    X Y A B A' B' A'' B'' : Set
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

{-

the tabulator of (X×E → E×Y) is a map τ : 1 → E (so, a point of E) such that 

tab × 1 ---id- 1 × tab 
   |             |          
  p×τ           τ×q
   |             |
   ↓             ↓
X × E -⟨d,s⟩⟶  E × Y

with the property that every ξ like

 U × 1 ---id---- 1 × U 
   |             | 
  f×e₀         e₀×g
   |             |
   ↓             ↓
X × E -⟨d,s⟩⟶  E × Y

factors as

 U × 1 ---id---- 1 × U 
   |             | 
  _×!           !×_
   |             |
   ↓             ↓
tab × 1 ---id- 1 × tab 
   |             |          
  p×τ           τ×q
   |             |
   ↓             ↓
X × E -⟨d,s⟩⟶  E × Y
-}

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


record CoTabulator {X Y} (M : Mealy X Y) : Set (suc zero) where
  private
    module M = Mealy M
  field
    cotab : Set
    p   : X → cotab
    q   : Y → cotab
    τ   : Cell p q M idMealy
    --
    universal : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) → 
      (cotab → U)
    fst-commute₁ : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) → 
      (universal ξ) ∘ p ≡ f
    snd-commute₁ : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) → 
      (universal ξ) ∘ q ≡ g
    commute₂ : ∀ {U} {f : X → U} {g : Y → U} (ξ : Cell f g M idMealy) → 
      Cell≡ ξ (subst₂ (λ Q R → Cell Q R M idMealy) (fst-commute₁ ξ) (snd-commute₁ ξ) (τ ⊙ᵥ idH (universal ξ)))



fatto : (M : Mealy X Y) → CoTabulator M 
fatto {X = X} {Y = Y} M = let module M = Mealy M in record 
  { cotab = X ⊎ Y 
  ; p = inj₁ 
  ; q = inj₂ 
  ; τ = record 
    { α = λ { x → tt } 
    ; com-s = λ { {x} {e} → {! M.s !} }
    ; com-d = {! !} -- refl 
    } 
  ; universal = λ { {f = f} ξ (inj₁ x) → f x
                  ; {g = g} ξ (inj₂ y) → g y } 
  ; fst-commute₁ = λ _ → refl 
  ; snd-commute₁ = λ _ → refl 
  ; commute₂ = λ { ξ → record { eq = {! Cell.com-d ξ !} } } 
  }

record SubobjectOfInterest (M : Mealy X Y) : Set (suc zero) where
  private 
    module M = Mealy M
  field
    e : M.E
    fix-d   : ∀ {x} → M.d (x , e) ≡ e 
    se-surj : ∀ {y} → ∃[ x ] (M.s (x , e) ≡ y)


fatto2 : (M : Mealy X Y) → (SOI : SubobjectOfInterest M) → Tabulator M 
fatto2 {X = X} {Y = Y} M SOI = 
  let module M = Mealy M 
      module SOI = SubobjectOfInterest SOI in
    record 
      { tab = X × Y
      ; p = proj₁
      ; q = proj₂
      ; τ = record
        { α = λ { _ → SOI.e }
        ; com-s = λ { {x , y} → {! proj₂ (SOI.se-surj {y}) !} }
        ; com-d = λ { {x , y} {tt} → SOI.fix-d }
        } 
      ; universal = λ { {f = f} {g = g} ξ → < f , g > }
      ; fst-commute₁ = λ { ξ → refl }
      ; snd-commute₁ = λ { ξ → refl }
      ; commute₂ = record { eq = λ { {x} → {! !} } } --impossible
      }




  -- TODO:
  -- define companions and conjoints
  -- prove that they do (not) exist.
