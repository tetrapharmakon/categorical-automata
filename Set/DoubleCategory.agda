{-# OPTIONS --allow-unsolved-metas #-}
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
    X Y Z A B C A' B' A'' B'' : Set
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
  ; com-s = {! !}
  ; com-d = {! !}
  }

unitorᴿ : ∀ (M : Mealy X Y) → Cell id id (idMealy ⋄ M) M
unitorᴿ M = record
  { α = λ { (e , _) → e }
  ; com-s = {! !}
  ; com-d = {! !}
  }

unitorᴸ⁻¹ : ∀ (M : Mealy X Y) → Cell id id (M ⋄ idMealy) M
unitorᴸ⁻¹ M = record
  { α = λ { (_ , e) → e }
  ; com-s = {! !}
  ; com-d = {!  !}
  }

unitorᴿ⁻¹ : ∀ (M : Mealy X Y) → Cell id id M (idMealy ⋄ M)
unitorᴿ⁻¹ M = record
  { α = λ { x → x , tt }
  ; com-s = {!  !}
  ; com-d = {!  !}
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
    ; com-d = refl -- refl
    }
  ; universal = λ { {f = f} ξ (inj₁ x) → f x
                  ; {g = g} ξ (inj₂ y) → g y }
  ; fst-commute₁ = λ _ → refl
  ; snd-commute₁ = λ _ → refl
  ; commute₂ = λ { ξ → record { eq = Cell.com-d ξ } }
  }

-- record SubobjectOfInterest (M : Mealy X Y) : Set (suc zero) where
--   private
--     module M = Mealy M
--   field
--     e : M.E
--     fix-d   : ∀ {x} → M.d (x , e) ≡ e
--     se-surj : ∀ {y} → ∃[ x ] (M.s (x , e) ≡ y)


-- fatto2 : (M : Mealy X Y) → (SOI : SubobjectOfInterest M) → Tabulator M
-- fatto2 {X = X} {Y = Y} M SOI =
--   let module M = Mealy M
--       module SOI = SubobjectOfInterest SOI in
--     record
--       { tab = X × Y
--       ; p = proj₁
--       ; q = proj₂
--       ; τ = record
--         { α = λ { _ → SOI.e }
--         ; com-s = λ { {x , y} → {! proj₂ (SOI.se-surj {y}) !} }
--         ; com-d = λ { {x , y} {tt} → SOI.fix-d }
--         }
--       ; universal = λ { {f = f} {g = g} ξ → < f , g > }
--       ; fst-commute₁ = λ { ξ → refl }
--       ; snd-commute₁ = λ { ξ → refl }
--       ; commute₂ = record { eq = λ { {x} → {! !} } } --impossible
--       }

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

-- I think conjoints do not exist
--
--
ConjointExperiment : (f : A → B) → (a : A) → Conjoint f
ConjointExperiment {A} {B} f a = record
  { conj = record
    { E = A × B
    ; d = λ { (b , (a , b')) → a , f a }
    ; s = λ { (b , (a , b')) → a }
    }
  ; Λ = record
    { α = λ { tt → a , f a }
    ; com-s = λ { {x} {tt} → {!  !} }
    ; com-d = refl
    }
  ; Ξ = record
    { α = λ { x → tt }
    ; com-s = λ { {b} {(a , b')} → {!  !} } -- b ≡ f a
    ; com-d = refl
    }
  ; zig = record { eq = refl }
  ; zag = record { eq = {!  !} }
  }

ConjointExperiment2 : (f : A → B) → Conjoint f
ConjointExperiment2 {A} {B} f = record
  { conj = {! mealify (P∞ A)  !}
  ; Λ = {!  !}
  ; Ξ = {!  !}
  ; zig = {!  !}
  ; zag = {!  !}
  }
-- initials and terminals

record DoubleTerminal : Set (suc zero) where
  field
    ⊤⊤ : Set
    universal₁ : ∀ {X Y} (M : Mealy X Y) → (X → ⊤⊤) × (Y → ⊤⊤)
    universal₂ : ∀ {X Y} (M : Mealy X Y) → Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) M idMealy
    unique : ∀ {X Y} {M : Mealy X Y} {c : Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) M idMealy} → Cell≡ c (universal₂ M)

record DoubleInitial : Set (suc zero) where
  field
    Ø : Set
    universal₁ : ∀ {X Y} (M : Mealy X Y) → (Ø → X) × (Ø → Y)
    universal₂ : ∀ {X Y} (M : Mealy X Y) → Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) idMealy M
    unique : ∀ {X Y} {M : Mealy X Y} {c : Cell (proj₁ (universal₁ M)) (proj₂ (universal₁ M)) idMealy M} → Cell≡ c (universal₂ M)


record DoubleSum (A B : Set) : Set (suc zero) where
  field
    sum : Set
    in₁ : A → sum
    in₂ : B → sum
    ι₁ : Cell in₁ in₁ idMealy idMealy
    ι₂ : Cell in₂ in₂ idMealy idMealy
    universal₁ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} → 
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u) → 
      (sum → X) × (sum → Y)
    universal₂ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} → 
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  → 
      (Cell (proj₁ (universal₁ ξ₁ ξ₂)) (proj₂ (universal₁ ξ₁ ξ₂)) idMealy u)
    fst-commute₁ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} → 
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  → 
      (proj₁ (universal₁ ξ₁ ξ₂) ∘ in₁ ≡ a) × (proj₂ (universal₁ ξ₁ ξ₂) ∘ in₁ ≡ a')
    snd-commute₁ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} → 
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  → 
      (proj₁ (universal₁ ξ₁ ξ₂) ∘ in₂ ≡ b) × (proj₂ (universal₁ ξ₁ ξ₂) ∘ in₂ ≡ b')
    fst-commute₂ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} → 
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  → 
      (Cell≡ ξ₁ (subst₂ (λ Q R → Cell Q R idMealy u) (proj₁ (fst-commute₁ ξ₁ ξ₂)) (proj₂ (fst-commute₁ ξ₁ ξ₂)) (ι₁ ⊙ᵥ universal₂ ξ₁ ξ₂)))
    snd-commute₂ : ∀ {u : Mealy X Y} {a : A → X} {a' : A → Y} {b : B → X} {b' : B → Y} → 
      (ξ₁ : Cell a a' idMealy u) (ξ₂ : Cell b b' idMealy u)  → 
      (Cell≡ ξ₂ (subst₂ (λ Q R → Cell Q R idMealy u) (proj₁ (snd-commute₁ ξ₁ ξ₂)) (proj₂ (snd-commute₁ ξ₁ ξ₂)) (ι₂ ⊙ᵥ universal₂ ξ₁ ξ₂)))



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

coscimmia : (M : Mealy X Y) → (e : Mealy.E M) → DoubleInitial
coscimmia M e = record
  { Ø = ⊥
  ; universal₁ = λ { M → (λ { () }) , λ { () } }
  ; universal₂ = λ { M → record
    { α = λ { tt → {!e !} }
    ; com-s = λ { {()} }
    ; com-d = λ { {()} }
    } }
  ; unique = record { eq = λ { {tt} → {!  !} } }
  }


-- fleshoutCellFromOne : {f : X → A} {g : X → B} {M : Mealy A B} → (e : Mealy.E M) → Cell f g idMealy M 
-- fleshoutCellFromOne e0 = record 
--   { α = λ { x → e0 } 
--   ; com-s = {! !} 
--   ; com-d = {! !} 
--   }
--

postulate
  dis : ∀ (M : Mealy X Y) → Mealy.E M 

candidateDblSum : DoubleSum A B 
candidateDblSum {A = A} {B = B} = record 
  { sum = A ⊎ B 
  ; in₁ = inj₁ 
  ; in₂ = inj₂ 
  ; ι₁ = record 
    { α = λ { x → x } 
    ; com-s = refl 
    ; com-d = refl 
    } 
  ; ι₂ = record 
    { α = λ { x → tt } 
    ; com-s = refl 
    ; com-d = refl 
    } 
  ; universal₁ = λ { {a = a} {a' = a'} {b = b} {b' = b'}
    ξ₁ ξ₂ → (λ { (inj₁ x) → a x
               ; (inj₂ y) → b y }) 
          , (λ { (inj₁ x) → a' x
               ; (inj₂ y) → b' y }) }
  ; universal₂ = λ { {u = u} {a = a} {a' = a'} {b = b} {b' = b'}
       ξ₁ ξ₂ → record 
            { α = λ { tt → dis u } 
            ; com-s = λ { {inj₁ x} {tt} → {! Cell.com-s ξ₁  !} 
                        ; {inj₂ y} {tt} → {! Cell.com-s ξ₂ !} } 
            ; com-d = λ { {x} {tt} → {! !} } 
            } } 
  ; fst-commute₁ = λ { ξ₁ ξ₂ → refl , refl } 
  ; snd-commute₁ = λ { ξ₁ ξ₂ → refl , refl} 
  ; fst-commute₂ = λ { ξ₁ ξ₂ → record { eq = {! !} } } 
  ; snd-commute₂ = λ { ξ₁ ξ₂ → record { eq = {! !} } } 
  }
