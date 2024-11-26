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

_⊙ₕ_ : ∀ {lv : A → X} {rv : C → Z} {M' : Mealy A B} {M : Mealy B C} {N' : Mealy X Y} {N : Mealy Y Z} {rh : Mealy A' B'} {boh : B → Y}
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
  ; com-d = {! !} 
  }

unitorᴿ⁻¹ : ∀ (M : Mealy X Y) → Cell id id M (idMealy ⋄ M)
unitorᴿ⁻¹ M = record 
  { α = λ { x → x , tt } 
  ; com-s = {! !} 
  ; com-d = {! !} 
  }

assoc : ∀ {M : Mealy X Y} {N : Mealy Y Z} {P : Mealy Z A} → Cell id id (P ⋄ (N ⋄ M)) ((P ⋄ N) ⋄ M)
assoc {M = M} {N = N} {P = P} = record 
  { α = λ { ((e , f) , p) → e , f , p } 
  ; com-s = refl 
  ; com-d = refl 
  } where module M = Mealy M
          module N = Mealy N
          module P = Mealy P

assoc⁻¹ : ∀ {M : Mealy X Y} {N : Mealy Y Z} {P : Mealy Z A} → Cell id id ((P ⋄ N) ⋄ M) (P ⋄ (N ⋄ M)) 
assoc⁻¹ {M = M} {N = N} {P = P} = record 
  { α = λ { (e , f , p) → (e , f) , p } 
  ; com-s = refl 
  ; com-d = refl 
  } where module M = Mealy M
          module N = Mealy N
          module P = Mealy P

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
    ; com-s = λ { {x} {tt} → {! !} }
    ; com-d = refl 
    } 
  ; Ξ = record 
    { α = λ { x → tt } 
    ; com-s = λ { {b} {(a , b')} → {! !} } -- b ≡ f a
    ; com-d = refl 
    }
  ; zig = record { eq = refl } 
  ; zag = record { eq = {! !} } 
  }

ConjointExperiment2 : (f : A → B) → Conjoint f 
ConjointExperiment2 {A} {B} f = record 
  { conj = {! mealify (P∞ A) !} 
  ; Λ = {! !} 
  ; Ξ = {! !} 
  ; zig = {! !} 
  ; zag = {! !} 
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


--record DoubleSum (A B : Set) : Set (suc zero) where
  --field
    --A⊎B : Set
    --in₁ : A → A⊎B
    --in₂ : B → A⊎B
    --universal₂ : ∀ {X Y A} {M : Mealy X Y} {f : A → X} {f' : A → Y} {ξ : Cell f f' idMealy M} {g : B → X} {g' : B → Y} {θ : Cell g g' idMealy M} → {! !}



scimmia : DoubleTerminal 
scimmia = record 
  { ⊤⊤ = ⊤ 
  ; universal₁ = λ { M → (λ { x → tt }) , λ { x → tt } }
  ; universal₂ = λ { M → record 
    { α = λ { x → tt } 
    ; com-s = refl 
    ; com-d = refl } 
    } 
  ; unique = record { eq = refl } 
  }

--open import Function.Bundles using (Bijection)

--⊥×W≅⊥ : {A} → Bijection ? -- ⊥ (⊥ × A)
--⊥×W≅⊥ = ?

to : {A} → ⊥ → ⊥ × A
to = λ { () }

from : {A} → ⊥ × A → ⊥
from = λ { () }

bijTo : ∀ {A} {x} → ((to {A}) ∘ (from {A})) x ≡ x
bijTo {x = () , a}

bijFrom : ∀ {A} {x} → ((from {A}) ∘ (to {A})) x ≡ x
bijFrom = refl

coscimmia : DoubleInitial
coscimmia = record 
  { Ø = ⊥ 
  ; universal₁ = λ { M → (λ { () }) , λ { () } }
  ; universal₂ = λ { M → record 
    { α = {! !} 
    ; com-s = λ { {()} }
    ; com-d = λ { {()} } 
    } } 
  ; unique = record { eq = λ { {tt} → {! !} } }
  }


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
    -- a ⊛ (e ∙ e') ≡ (a ⊛ e) ∙ ((a ◁ e) ⊛ e')
    -- it's a twisted homomorphism!
    -- a ⊛ (e ∙ e') ≡ (a ⊛ e) ∙ aᵉ ⊛ e'
    -- estensione alle liste?
    -- (a ∷ b) ⊛ (e ∙ e') ≡ ⟨ definition ⟩
    -- a ⊛ (b ⊛ (e ∙ e')) ≡ ⟨ cong a ⊛ _ ⟩
    -- a ⊛ ((b ⊛ e) ∙ (bᵉ ⊛ e'))
    -- a ⊛ (b ⊛ e) ∙ (a ◁ (b ⊛ e)) ⊛ (bᵉ ⊛ e'))
    -- ([a,b] ⊛ e) ∙ ([aᵇᵒᵉ,bᵉ] ⊛ e')
    --
    --
    --
record RightExtension (F : Mealy A B) (G : Mealy A C) : Set (suc zero) where
  field
    Ran : Mealy B C 
    ρ : Cell id id (Ran ⋄ F) G
    universal : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) → Cell id id H Ran
    commute : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) → Cell≡ ξ ((idCell F ⊙ₕ universal H ξ) ⊙ᵥ ρ)
    unique : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) (c : Cell id id H Ran) (pc : Cell≡ ξ ((idCell F ⊙ₕ c) ⊙ᵥ ρ)) → Cell≡ c (universal H ξ)

record _isRan_along_ (Ran : Mealy B C) (G : Mealy A C) (F : Mealy A B) : Set (suc zero) where
  field
    ρ : Cell id id (Ran ⋄ F) G
    universal : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) → Cell id id H Ran
    commute : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) → Cell≡ ξ ((idCell F ⊙ₕ universal H ξ) ⊙ᵥ ρ)
    unique : ∀ (H : Mealy B C) (ξ : Cell id id (H ⋄ F) G) (c : Cell id id H Ran) (pc : Cell≡ ξ ((idCell F ⊙ₕ c) ⊙ᵥ ρ)) → Cell≡ c (universal H ξ)

Ran_⟨_⟩ : (F : Mealy A B) (G : Mealy A C) → Mealy B C 
Ran_⟨_⟩ F G = record 
  { E = (F.E → G.E)
  ; d = λ { (b , u) → λ { x → u x } }
  ; s = λ { (b , u) → G.s ({! !} , u {! !}) } 
  } where module F = Mealy F 
          module G = Mealy G


piollo : (F : Mealy A B) (G : Mealy A C) → RightExtension F G 
piollo F G = record 
  { Ran = Ran F ⟨ G ⟩ 
  ; ρ = record 
    { α = λ { (e' , u) → u e' } 
    ; com-s = λ { {a} {e' , u} → {! !} } -- axioms of Mealy morphisms?
    ; com-d = λ { {a} {e' , u} → {! !} }
    }   
  ; universal = {! !} 
  ; commute = {! !} 
  ; unique = {! !} 
  } where module F = Mealy F 
          module G = Mealy G

module _ {F : Mealy A B} {G : Mealy A C} {R : Mealy B C} where
  
  module F = Mealy F 
  module G = Mealy G
  module R = Mealy R


  fallo : (H : Mealy B C) → (ρ : F.E → R.E → G.E)
    → R isRan G along F 
  fallo H ρ = record 
    { ρ = record 
      { α = λ { (f , r) → ρ f r } -- ρ : F.E × R.E → G.E 
      ; com-s = λ { {a} {f , r} → {! !} } -- Goal: G.s (a , ρ f r) ≡ R.s (F.s (a , f) , r)
      ; com-d = λ { {a} {f , r} → {! !} } -- Goal: G.d (a , ρ f r) ≡ ρ (F.d (a , f)) (R.d (F.s (a , f) , r))
      } 
    ; universal = λ { H ξ → let module H = Mealy H 
                                module ξ = Cell ξ in record 
      { α = {!ν !} -- Goal: ν : H.E → R.E
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

record LeftExtension (F : Mealy A B) (G : Mealy A C) : Set (suc zero) where
  field
    Lan : Mealy C B 
    η : Cell id id F (Lan ⋄ G)
    universal : ∀ (H : Mealy C B) (ξ : Cell id id F (H ⋄ G)) → Cell id id Lan H
    commute : ∀ (H : Mealy C B) (ξ : Cell id id F (H ⋄ G)) → Cell≡ ξ (η ⊙ᵥ (idCell G ⊙ₕ universal H ξ)) -- ((idCell F ⊙ₕ universal H ξ) ⊙ᵥ ρ)
    unique : ∀ (H : Mealy C B) (ξ : Cell id id F (H ⋄ G)) (c : Cell id id Lan H) (pc : Cell≡ ξ (η ⊙ᵥ (idCell G ⊙ₕ universal H ξ))) → Cell≡ c (universal H ξ)

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

  azzo : (H : Mealy B C) → (η : X.E → Y.E × L.E)
    → L isLan X along Y 
  azzo H η = record 
    { universal = λ { H ξ → let module H = Mealy H 
                                module ξ = Cell ξ in record 
      { α = {!ν !} -- nu
      ; com-s = λ { {b} {h} → {! !} } --
--Goal: H.s (b , nu h) ≡ L.s (b , h)
      ; com-d = λ { {b} {h} → {! !} } --
--Goal: H.d (b , nu h) ≡ nu (L.d (b , h))
      } } 
    ; commute = λ { H ξ → {! !} } --
    ; unique = λ { H ξ c pc → {! !} } --
    }


