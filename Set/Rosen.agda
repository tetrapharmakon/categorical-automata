module Set.Rosen where

open import Set.Automata
open import Data.Sum
open import Data.Product
open import Function using (_∘_; id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)

private
  variable
    A B C D E F I O : Set

record MR (A B : Set) : Set₁ where
  eta-equality
  field
    f : A → B
    ϕ : ∀ {X} → X → (A → X)

  ϕf = ϕ {X = B}
  ϕf∘f = ϕf ∘ f

open MR

-- record MR2 (A B : Set) : Set₁ where
--   eta-equality
--   field
--     f : A → B
--     ϕ1 : B → (A → B)
--     ϕ2 : (A → B) → (B → (A → B))

-- record MR⇒ (X : MR A B) (Y : MR C D) : Set₁ where 
--   eta-equality
--   module X = MR X 
--   module Y = MR Y
--   field
--     u : A → C 
--     v : B → D 
--     comp-f : ∀ a → Y.f (u a) ≡ v (X.f a)
--     comp-ϕ : ∀ b → ∀ a → v (X.ϕ b a) ≡ Y.ϕ (v b) (u a)

-- _＠_ : {X : MR A B} {Y : MR C D} {Z : MR E F} (h : MR⇒ X Y) (k : MR⇒ Y Z) → MR⇒ X Z
-- _＠_ {X = X} {Y = Y} {Z = Z} h k = 
--   let module X = MR X
--       module Y = MR Y
--       module Z = MR Z 
--       module h = MR⇒ h 
--       module k = MR⇒ k in record 
--     { u = k.u ∘ h.u 
--     ; v = k.v ∘ h.v 
--     ; comp-f = λ { a → trans (k.comp-f (h.u a)) (cong k.v (h.comp-f a)) } 
--     ; comp-ϕ = λ { b a → trans (cong k.v (h.comp-ϕ b a)) (k.comp-ϕ (h.v b) (h.u a)) } 
--     } 

-- 𝟙 : {X : MR A B} → MR⇒ X X
-- 𝟙 = record 
--   { u = Function.id 
--   ; v = Function.id 
--   ; comp-f = λ { a → refl } 
--   ; comp-ϕ = λ { b a → refl } 
--   }

⟦_⟧ : MR I O → Mealy I O 
⟦_⟧ {I} {O} M = record 
 { E = I → O 
 ; d = λ { (i , f) i' → M.ϕ (f i) i' } 
 ; s = λ { (i , f) → f i } 
 } where module M = MR M

-- ⟦_⟧' : MR2 I O → Mealy I (O × (O → I → O)) 
-- ⟦_⟧' {I} {O} M = record 
--   { E = (I → O) × (O → I → O)
--   ; d = λ { (i , (u , T)) → (λ { j → M.ϕ2 (M.ϕ1 (T (u i) j)) (u i) j }) , T }
--   ; s = λ { (i , (u , T)) → u i , T }
--   } where module M = MR2 M


-- ⟦_⟧2 : MR2 I O → Mealy I O
-- ⟦_⟧2 {I} {O} M = record 
--   { E = (I → O) × (O → I → O)
--   ; d = λ { (i , (u , T)) → M.ϕ2 (M.ϕ1 (u i)) (u i) , T } 
--   ; s = λ { (i , (u , T)) → u i } 
--   } where module M = MR2 M

-- fagiano : (y : MR B C) → (x : MR A B) → Mealy.E (⟦ y ⟧ ⋄ ⟦ x ⟧) 
--   ≡ Σ (A → B) (λ x₁ → (B → C))
-- fagiano y x = refl

-- pollo : (y : MR B C) → (x : MR A B) → Mealy.d (⟦ y ⟧ ⋄ ⟦ x ⟧) 
--   ≡ λ { (a , (u , t)) → (ϕ x (u a)) , (ϕ y (t (u a))) }
-- pollo y x = refl

-- papero : (y : MR B C) → (x : MR A B) → Mealy.s (⟦ y ⟧ ⋄ ⟦ x ⟧) 
--   ≡ λ { (a , (u , t)) → t (u a) }
-- papero y x = refl

-- pollo2 : (y : MR2 B C) → (x : MR2 A B) → Mealy.d (⟦ y ⟧2 ⋄ ⟦ x ⟧2) 
--   ≡ λ { (a , ((u , K) , (v , T))) → Mealy.d ⟦ x ⟧2 (a , u , K) , Mealy.d ⟦ y ⟧2 (u a , v , T) }
-- pollo2 y x = refl

-- papero2 : (y : MR2 B C) → (x : MR2 A B) → Mealy.s (⟦ y ⟧2 ⋄ ⟦ x ⟧2) 
--   ≡ λ { (a , ((u , K) , (v , T))) → v (u a) }
-- papero2 y x = refl


--cecck-morphisms : {X : MR A B} {Y : MR C D} (h : MR⇒ X Y) → Mealy⇒ ⟦ X ⟧ ⟦ Y ⟧
--cecck-morphisms = ?
--
--
-- record StortoMealy (I : Set) (O : Set) : Set₁ where
--   eta-equality
--   field
--     S : Set
--     b : O → S
--     σ : I × S → O

-- open StortoMealy

-- μ : (x : StortoMealy A B) → Mealy A B
-- μ x = record 
--   { E = x.S 
--   ; d = x.b ∘ x.σ 
--   ; s = x.σ 
--   } where module x = StortoMealy x

{-
dcompo-test : (x : StortoMealy A B) (y : StortoMealy B C) → Mealy.d ((μ y) ⋄ (μ x)) 
  ≡ λ { (a , (s , s')) → b x (σ x (a , s)) , b y (σ y (σ x (a , s) , s')) }
dcompo-test x y = refl
  where module x = StortoMealy x


scompo-test : (x : StortoMealy A B) (y : StortoMealy B C) → Mealy.s ((μ y) ⋄ (μ x)) 
  ≡ λ { (a , (s , s')) → σ y (σ x (a , s) , s') }
scompo-test x y = refl


stortoComp : (x : StortoMealy A B) (y : StortoMealy B B) → StortoMealy A B 
stortoComp x y = record 
  { S = x.S × y.S 
  ; b = < x.b , y.b >
  ; σ = λ { (a , (p , q)) → y.σ (x.σ (a , p) , q) } 
  } where module x = StortoMealy x
          module y = StortoMealy y

stortoComp' : (x : StortoMealy A A) (y : StortoMealy A B) → StortoMealy A B
stortoComp' x y = record 
  { S = x.S × y.S 
  ; b =  λ { b → {! x.b !} , {! y.b !} }
  ; σ = {! !}
  } where module x = StortoMealy x
          module y = StortoMealy y

--
--
-}
MRfunctor : {A A' B B' : Set} → (u : A' → A) (v : B → B') → MR A B → MR A' B' 
MRfunctor {A} {A'} {B} {B'} u v x = record 
  { f = v ∘ x.f ∘ u 
  ; ϕ = λ { t a' → x.ϕ t (u a') } 
  } where module x = MR x


MRfunctor-ϕf : {A A' B B' : Set} → (u : A' → A) (v : B → B') → (M : MR A B) → ϕf (MRfunctor u v M) ≡ λ { b' a' → ϕ {B = B'} (MRfunctor id v M) {X = B'} b' (u a') }
MRfunctor-ϕf u v M = refl

MRfunctoriality-1 : {A A' A'' B B' B'' : Set} → 
  (u' : A'' → A') (u : A' → A) (v : B → B') (v' : B' → B'') (M : MR A B) → {X : Set} → 
  MR.ϕ (MRfunctor {A} {A''} {B} {B''} (u ∘ u') (v' ∘ v) M) {X} ≡ ϕ (MRfunctor u' v' (MRfunctor u v M)) {X}
MRfunctoriality-1 u' u v v' M {X} = refl

MRfunctoriality-1' : {A A' A'' B B' B'' : Set} → 
  (u' : A'' → A') (u : A' → A) (v : B → B') (v' : B' → B'') (M : MR A B) → {x : A''} → 
  MR.f (MRfunctor {A} {A''} {B} {B''} (u ∘ u') (v' ∘ v) M) x ≡ f (MRfunctor u' v' (MRfunctor u v M)) x
MRfunctoriality-1' u' u v v' M {x} = refl

MRfunctoriality-2 : {A B : Set} → MRfunctor {A} {A} {B} {B} id id ≡ id
MRfunctoriality-2 = refl


-- counità ?
ε : MR A B → A → B
ε M = f M 

mr1 : MR A A 
mr1 = record
  { f = id 
  ; ϕ = λ { x _ → x } 
  }

Mealy-di-mr1 : {A : Set} → ⟦ mr1 ⟧ ≡ record 
  { E = A → A 
  ; d = λ { (a , f) a' → f a } 
  ; s = λ { (a , f) → f a } 
  }
Mealy-di-mr1 = refl

-- comult ? Serve una classe di equivalenza in ∫^X MR(A,X) × MR(X,B);
-- può essere nel sommando ad X=A, oppure X=B e poi dovranno (forse)
-- essere uguali nel quoziente della coend
δA : MR A B → MR A A × MR A B 
δA M = mr1 , M


δB : MR A B → MR A B × MR B B 
δB M = M , mr1

-- sono uguali?
-- sì

fattoide : (M : MR A B) → ∀ x → f (MRfunctor (f M) id mr1) x ≡ f M x
fattoide M x = refl

fattoide' : (M : MR A B) → ∀ X t a → ϕ (MRfunctor (f M) id mr1) {X} t a ≡ t 
fattoide' M X t a = refl


fattoide2 : (M : MR A B) → ∀ x → f (MRfunctor id (f M) mr1) x ≡ f M x
fattoide2 M x = refl

fattoide2' : (M : MR A B) → ∀ X t a → ϕ (MRfunctor id (f M) mr1) {X} t a ≡ t 
fattoide2' M X t a = refl

-- counità + comult interagiscono ovviamente (posso scegliere ogni volta la rappresentazione per delta che non viene toccata da ε)
-- coassoc? Difficile da agdare, facile a mano.


record Dgnz : Set₁ where
  field
    diel : MR A A 
    ε-comm : ε {A} diel ≡ id
    δA-comm : proj₂ (δA {A} diel) ≡ mr1
    δB-comm : proj₁ (δB {B} diel) ≡ mr1
    -- sono ridondanti

open Dgnz

-- eqrel della coend identifica costanti? Prolly la parte Phi è trivialized nel diagonizz
dis : {X Y : Set} → (f : X → Y) → (MR A X) × (MR X B) → (MR A Y) × (MR X B)
dis {X} {Y} f = Data.Product.map₁ (MRfunctor id f)

dat : {X Y : Set} → (f : X → Y) → (MR A Y) × (MR Y B) → (MR A Y) × (MR X B)
dat {X} {Y} f = Data.Product.map₂ (MRfunctor f id)

prova : {X Y : Set} → (f : X → Y) → (m : MR A B) → Set₁
prova f m = let l = dis f ({!   !} , {!   !}) in {!   !}

module _ (x : MR A B) where
  contuzzo : (⟦ mr1 ⟧ ⋄ ⟦ x ⟧) ≡ record 
    { E = (A → B) × (B → B)
    ; d = λ { (a , e , e') → (λ { a' → ϕ x (e a) a' }) , λ { b → e' (e a) } }
    ; s = λ { (a , e , e') → e' (e a) }
    }
  contuzzo = refl


  verifica : Mealy⇒ (⟦ x ⟧) (⟦ mr1 ⟧ ⋄ ⟦ x ⟧)
  verifica = record 
    { hom = λ { t → t , id } 
    ; d-eq = λ { (a , t) → cong₂ _,_ refl {! !} } -- unfillable!
    ; s-eq = λ { (a , t) → {! !} } 
    }

  coverifica : Mealy⇒ (⟦ mr1 ⟧ ⋄ ⟦ x ⟧) (⟦ x ⟧) 
  coverifica = record 
    { hom = λ { (f , u) a → f a } 
    ; d-eq = λ { (a , f , u) → refl } 
    ; s-eq = λ { (a , f , u) → {! !} } 
    }

