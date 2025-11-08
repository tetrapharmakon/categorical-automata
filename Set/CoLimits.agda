{-# OPTIONS --allow-unsolved-metas #-}
module Set.CoLimits where

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


coTensor : Tabulator (idMealy {A})
coTensor {A = A} = record 
  { tab = A × A 
  ; p = proj₁ 
  ; q = proj₂ 
  ; τ = record 
    { α = λ { x → tt } 
    ; com-s = λ { {a , a'} {tt} → {! !} }
    ; com-d = λ { {a , a'} {tt} → refl }
    } 
  ; universal = λ { {f = f} {g = g} ξ → < f , g > } 
  ; fst-commute₁ = λ { ξ → refl } 
  ; snd-commute₁ = λ { ξ → refl } 
  ; commute₂ = record { eq = refl } 
  }


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


fatto2 : (M : Mealy X Y) → (e : Mealy.E M) → Tabulator M
fatto2 {X = X} {Y = Y} M e =
 let module M = Mealy M in
   record
     { tab = X × Y
     ; p = proj₁
     ; q = proj₂
     ; τ = record
       { α = λ tt → e
       ; com-s = λ { {x , y} → {! proj₂ (SOI.se-surj {y}) !} }
       ; com-d = λ { {x , y} {tt} → {! !} }
       }
     ; universal = λ { {f = f} {g = g} ξ → < f , g > }
     ; fst-commute₁ = λ { ξ → refl }
     ; snd-commute₁ = λ { ξ → refl }
     ; commute₂ = record { eq = λ { {x} → {! !} } } --impossible
     }

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
--
record Graph (f : A → B) : Set where 
  field
    fst : A 
    snd : B 
    fa≡b : f fst ≡ snd
--

embed : (f : A → B) → (Γf : Graph f) → A × B
embed f Γf = Γf.fst , Γf.snd
  where module Γf = Graph Γf

granchiollo : (f : A → B) → Tabulator (Companion.comp (f ₒ))
granchiollo {A = A} {B = B} f = record 
  { tab = Graph f -- A × B 
    ; p = proj₁ ∘ embed f -- proj₁
    ; q = proj₂ ∘ embed f -- proj₁
    ; τ = record 
      { α = λ { x → x } 
      ; com-s = λ { {Γf} → let module Γf = Graph Γf in Γf.fa≡b }
      ; com-d = λ { {t} → refl }
      } 
    ; universal = λ { ξ x → {! !} } -- a certain pair (a , fa); but for which a? 
    ; fst-commute₁ = λ { ξ → {! !} } 
    ; snd-commute₁ = λ { ξ → {! !} } 
    ; commute₂ = record { eq = λ { {tt} → {! !} } }
  } 
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

ConjointExperiment2 : 
  (f : A → B) 
  (E : Set) 
  (e₀ : E) 
  (d : B × E → E) 
  (s : B × E → A) → Conjoint f
ConjointExperiment2 {A} {B} f E e₀ d s = record
  { conj = record 
    { E = E
    ; d = d -- d : B × E → E
    ; s = s -- s : B × E → A
    }
  ; Λ = record 
    { α = λ { tt → e₀ } -- E pointed
    ; com-s = λ { {a} {tt} → {! !} } -- s (f a , e₀) ≡ a
    ; com-d = λ { {a} {tt} → {! !} } -- d (f a , e₀) ≡ e₀
    }
  ; Ξ = record 
    { α = λ { x → tt } 
    ; com-s = λ { {b} {e} → {! !} } -- b ≡ f (s (b , e))
    ; com-d = λ { {b} {e} → refl }
    }
  ; zig = record { eq = refl }
  ; zag = record { eq = {! !} }
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
        {c : ∀ {t} → f (x t) ≡ g (y t) } 
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) } 
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) → 
          (U → pb) × (V → pb)
    universal₂ : 
      ∀ {u : Mealy U V} 
        {x : U → X} 
        {x' : V → X} 
        {y : U → Y} 
        {y' : V → Y} 
        {c : ∀ {t} → f (x t) ≡ g (y t) } 
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) } 
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) → 
          (Cell (proj₁ (universal₁ ξ₁ ξ₂)) (proj₂ (universal₁ ξ₁ ξ₂)) u idMealy)
    fst-commute₁ : 
      ∀ {u : Mealy U V} 
        {x : U → X} 
        {x' : V → X} 
        {y : U → Y} 
        {y' : V → Y} 
        {c : ∀ {t} → f (x t) ≡ g (y t) } 
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) } 
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) → 
          (pX ∘ proj₁ (universal₁ ξ₁ ξ₂) ≡ x) × (pX ∘ proj₂ (universal₁ ξ₁ ξ₂) ≡ x')
    snd-commute₁ : 
      ∀ {u : Mealy U V} 
        {x : U → X} 
        {x' : V → X} 
        {y : U → Y} 
        {y' : V → Y} 
        {c : ∀ {t} → f (x t) ≡ g (y t) } 
        {c' : ∀ {t} → f (x' t) ≡ g (y' t) } 
        (ξ₁ : Cell x x' u idMealy) (ξ₂ : Cell y y' u idMealy) → 
          (pY ∘ proj₁ (universal₁ ξ₁ ξ₂) ≡ y) × (pY ∘ proj₂ (universal₁ ξ₁ ξ₂) ≡ y')
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
           (proj₂ (fst-commute₁ ξ₁ ξ₂)) (universal₂ ξ₁ ξ₂ ⊙ᵥ πX))
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
           (proj₂ (snd-commute₁ ξ₁ ξ₂)) (universal₂ ξ₁ ξ₂ ⊙ᵥ πY))

          

-- record DoubleComma (f : A → X) (M : Mealy B X) : Set (suc zero) where
--   field
--     comma : Set
--     P : Mealy comma A 
--     q : comma → B -- two projections
--     φ : Cell q f P M
--     --
--     h-universal₁ : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → (U → comma)
--     h-commute₀ : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → ∀ {u : U} → q ∘ (h-universal₁ ξ) ≡ g
--     h-universal₂ : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → Cell (h-universal₁ ξ) h idMealy P
--     h-commute : ∀ {h : U → A} {g : U → B} (ξ : Cell g (f ∘ h) idMealy M) → Cell≡ ξ (subst (λ t → Cell t (f ∘ h) idMealy M) (h-commute₀ ξ) (h-universal₂ ξ ⊙ᵥ φ))


-- candidateDblComma : (f : A → X) (M : Mealy B X) (C : Set) → DoubleComma f M 
-- candidateDblComma f M C = record 
--  { comma = C 
--  ; P = record 
--    { E = {! !} 
--    ; d = {! !} 
--    ; s = {! !} 
--    } 
--  ; q = {! !} 
--  ; φ = {! !} 
--  ; h-universal₁ = {! !} 
--  ; h-commute₀ = {! !} 
--  ; h-universal₂ = {! !} 
--  ; h-commute = {! !} 
--  }


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

-- testInitial : (M : Mealy X Y) → (e : Mealy.E M) → DoubleInitial
-- testInitial M e = record
--   { Ø = ⊥
--   ; universal₁ = λ { M → (λ { () }) , λ { () } }
--   ; universal₂ = λ { M → record
--     { α = λ { tt → {!e !} }
--     ; com-s = λ { {()} }
--     ; com-d = λ { {()} }
--     } }
--   ; unique = record { eq = λ { {tt} → {!  !} } }
--   }


-- fleshoutCellFromOne : {f : X → A} {g : X → B} {M : Mealy A B} → (e : Mealy.E M) → Cell f g idMealy M 
-- fleshoutCellFromOne e0 = record 
--   { α = λ { x → e0 } 
--   ; com-s = {! !} 
--   ; com-d = {! !} 
--   }
--

-- postulate
--   dis : ∀ (M : Mealy X Y) → Mealy.E M 

-- candidateDblSum : DoubleSum A B 
-- candidateDblSum {A = A} {B = B} = record 
--   { sum = A ⊎ B 
--   ; in₁ = inj₁ 
--   ; in₂ = inj₂ 
--   ; ι₁ = record 
--     { α = λ { x → x } 
--     ; com-s = refl 
--     ; com-d = refl 
--     } 
--   ; ι₂ = record 
--     { α = λ { x → tt } 
--     ; com-s = refl 
--     ; com-d = refl 
--     } 
--   ; universal₁ = λ { {a = a} {a' = a'} {b = b} {b' = b'}
--     ξ₁ ξ₂ → (λ { (inj₁ x) → a x
--                ; (inj₂ y) → b y }) 
--           , (λ { (inj₁ x) → a' x
--                ; (inj₂ y) → b' y }) }
--   ; universal₂ = λ { {u = u} {a = a} {a' = a'} {b = b} {b' = b'}
--        ξ₁ ξ₂ → record 
--             { α = λ { tt → dis u } 
--             ; com-s = λ { {inj₁ x} {tt} → {! Cell.com-s ξ₁  !} 
--                         ; {inj₂ y} {tt} → {! Cell.com-s ξ₂ !} } 
--             ; com-d = λ { {x} {tt} → {! !} } 
--             } } 
--   ; fst-commute₁ = λ { ξ₁ ξ₂ → refl , refl } 
--   ; snd-commute₁ = λ { ξ₁ ξ₂ → refl , refl} 
--   ; fst-commute₂ = λ { ξ₁ ξ₂ → record { eq = {! !} } } 
--   ; snd-commute₂ = λ { ξ₁ ξ₂ → record { eq = {! !} } } 
--   }
  -- per ogni u, sceglie un punto del carrier di u, che sia sempre lo stesso; chiaramente, qesto non si può fare se u.E ha più di un elemento.



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
  ; universal₁ = λ { {x = x} {x' = x'} {y = y} {y' = y'} {c = c} {c' = c'} ξ₁ ξ₂ → 
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
  ; universal₂ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} {c = c} {c' = c'} ξ₁ ξ₂ → record 
    { α = λ { t → tt } 
    ; com-s = λ { {p} {q} → {! Cell.com-s ξ₂ !} }
    ; com-d = refl 
    } } 
  ; fst-commute₁ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} {c = c} {c' = c'} ξ₁ ξ₂ → 
    refl , refl } 
  ; snd-commute₁ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} {c = c} {c' = c'} ξ₁ ξ₂ → 
    refl , refl } 
  ; fst-commute₂ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} {c = c} {c' = c'} ξ₁ ξ₂ → 
    record { eq = λ { {x} → refl } } }  
  ; snd-commute₂ = λ {  {x = x} {x' = x'} {y = y} {y' = y'} {c = c} {c' = c'} ξ₁ ξ₂ → 
    record { eq = λ { {x} → refl } } }
  }
