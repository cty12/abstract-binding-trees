{-# OPTIONS --without-K --rewriting #-}
{-
   Cast Calculus partly based on a version 
   by Jeremy, Phil Wadler, and Peter Thiemann.
-}

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var

module rewriting.examples.Cast where

{- Base types -}

data Base : Set where
  ′ℕ : Base
  ′𝔹 : Base

{- Interpretation of base types into Agda types. -}

rep : Base → Set 
rep ′ℕ  =  ℕ
rep ′𝔹  =  𝔹

{- Types -}

infixr 7 _⇒_
infix  8 $ₜ_

data Type : Set where
  ★ : Type
  $ₜ_ : (ι : Base) → Type
  _⇒_ : (A : Type) → (B : Type) → Type

{- Ground types -}

infix  8 $ᵍ_

data Ground : Type → Set where
  $ᵍ_  :
       (ι : Base) 
       ------------
     → Ground ($ₜ ι)

  ★⇒★ :
       --------------
       Ground (★ ⇒ ★)

data GroundOf : Type → Type → Set where
  gnd-base : ∀{ι} → GroundOf ($ₜ ι) ($ₜ ι)
  gnd-fun : ∀{A B} → GroundOf (A ⇒ B) (★ ⇒ ★)

{- Terms -}

data Op : Set where
  op-lam : Op
  op-app : Op
  op-lit : ∀{ι : Base} → rep ι → Op
  op-cast : Type → Type → Op
  op-blame : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-lit n) = []
sig (op-cast A B) = ■ ∷ []
sig (op-blame) = []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term)

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆
infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $ k = (op-lit k) ⦅ nil ⦆
pattern _⟨_⇒_⟩ M A B = (op-cast A B) ⦅ cons (ast M) nil ⦆
pattern blame = (op-blame) ⦅ nil ⦆

data Value : Term → Set where
  ƛ̬_ : (N : Term) → Value (ƛ N)
  $̬_ : ∀{ι} → (k : rep ι) → Value ($ k)
  _〈_〉 : ∀{V G} → Value V → (g : Ground G) → Value (V ⟨ G ⇒ ★ ⟩)

value : ∀ {V : Term}
  → (v : Value V)
    -------------
  → Term
value {V = V} v  =  V  

open Renaming

rename-val : ∀ {V : Term}
  → (ρ : Rename)
  → Value V
    ------------------
  → Value (rename ρ V)
rename-val ρ (ƛ̬ N)    =  ƛ̬ (rename (extr ρ) N)
rename-val ρ ($̬ k)    =  $̬ k
rename-val ρ (V 〈 g 〉)  =  (rename-val ρ V) 〈 g 〉

sub-val : ∀ {V}
  → (σ : Subst)
  → Value V
  → Value (⟪ σ ⟫ V)
sub-val σ (ƛ̬ N) = ƛ̬ ⟪ ext σ ⟫ N
sub-val σ ($̬ k) = $̬ k
sub-val σ (V 〈 g 〉)  =  (sub-val σ V) 〈 g 〉

{----------------- Type System ------------------------}

infix 3 _⊢_⦂_

data _⊢_⦂_ : List Type → Term → Type → Set

data _⊢_⦂_ where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Γ} (ι : Base) {k : rep ι}
      -----------------
    → Γ ⊢ $ k ⦂ ($ₜ ι)

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢ƛ : ∀ {Γ N A B}
    → (A ∷ Γ) ⊢ N ⦂ B
      -----------------
    → Γ ⊢ ƛ N ⦂ (A ⇒ B)

  ⊢⟨⇒⟩ : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A
      --------------------
    → Γ ⊢ M ⟨ A ⇒ B ⟩ ⦂ B

  ⊢blame : ∀{Γ A}
      ---------------
    → Γ ⊢ blame ⦂ A

infix  6 □·_
infix  6 _·□
infix  6 □⟨_⇒_⟩

data Frame : Set where

  □·_ : 
      (M : Term)
      ----------
    → Frame

  _·□ : ∀ {V : Term}
    → (v : Value V)
      -------------
    → Frame

  □⟨_⇒_⟩ : 
      Type
    → Type
      -----
    → Frame

{- The plug function inserts an expression into the hole of a frame. -}

_⟦_⟧ : Frame → Term → Term
(□· M) ⟦ L ⟧        =  L · M
(v ·□) ⟦ M ⟧        =  value v · M
(□⟨ A ⇒ B ⟩) ⟦ M ⟧  =  M ⟨ A ⇒ B ⟩

{- Reduction -}

infix 2 _—→_
data _—→_ : Term → Term → Set where

  ξξ : ∀ {M N : Term} {M′ N′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ M ⟧
    → N′ ≡ F ⟦ N ⟧
    → M —→ N
      --------
    → M′ —→ N′

  ξξ-blame : ∀ {M′ : Term}
    → (F : Frame)
    → M′ ≡ F ⟦ blame ⟧
      ------------------
    → M′ —→ blame

  β : ∀ {N : Term} {W : Term}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  id-ι : ∀ {ι}{k : rep ι}
      ----------------------------
    → ($ k ⟨ $ₜ ι ⇒ $ₜ ι ⟩) —→ $ k

  id-★ : ∀ {V}
    → Value V
      ----------------------------
    → (V ⟨ ★ ⇒ ★ ⟩) —→ V

  wrap : ∀{A A′ B B′} {N : Term}
      -----------------------------------------------------------
    → (ƛ N ⟨ (A ⇒ B) ⇒ (A′ ⇒ B′) ⟩)
       —→ ƛ (((rename suc (ƛ N)) · ((` 0) ⟨ A′ ⇒ A ⟩)) ⟨ B ⇒ B′ ⟩)

  expand : ∀ {V : Term}{A G}
    → Value V
    → GroundOf A G
    → ¬ Ground A
      -----------------------------------------
    → (V ⟨ A ⇒ ★ ⟩) —→ (V ⟨ A ⇒ G ⟩) ⟨ G ⇒ ★ ⟩ 

  collapse : ∀{G} {V : Term}
    → Value V
    → (g : Ground G)
      ------------------------------
    → (V ⟨ G ⇒ ★ ⟩) ⟨ ★ ⇒ G ⟩ —→ V

  collide  : ∀{G H} {V : Term}
    → Value V
    → (g : Ground G)
    → (h : Ground H)
    → G ≢ H
      ---------------------------------
    → (V ⟨ G ⇒ ★ ⟩) ⟨ ★ ⇒ H ⟩ —→ blame

pattern ξ F M—→N = ξξ F refl refl M—→N
pattern ξ-blame F = ξξ-blame F refl

{- Reflexive and transitive closure of reduction -}

infixr 1 _++_
infix  1 begin_
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : (M : Term)
      ---------
    → M —↠ M

  _—→⟨_⟩_ : (L : Term) {M N : Term}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N : Term} → (M —↠ N) → (M —↠ N)
begin M—↠N = M—↠N

{- Convenience function to build a sequence of length one. -}

unit : ∀ {M N : Term} → (M —→ N) → (M —↠ N)
unit {M = M} {N = N} M—→N  =  M —→⟨ M—→N ⟩ N ∎


{- Apply ξ to each element of a sequence -}

ξ* : ∀ {M N : Term} → (F : Frame) → M —↠ N → F ⟦ M ⟧ —↠ F ⟦ N ⟧
ξ* F (M ∎) = F ⟦ M ⟧ ∎
ξ* F (L —→⟨ L—→M ⟩ M—↠N) = (F ⟦ L ⟧ —→⟨ ξ F L—→M ⟩ ξ* F M—↠N)

{- Concatenate two sequences. -}

_++_ : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
(M ∎) ++ M—↠N                =  M—↠N
(L —→⟨ L—→M ⟩ M—↠N) ++ N—↠P  =  L —→⟨ L—→M ⟩ (M—↠N ++ N—↠P)

{- Alternative notation for sequence concatenation. -}

_—↠⟨_⟩_ : (L : Term) {M N : Term}
  → L —↠ M
  → M —↠ N
    ---------
  → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N  =  L—↠M ++ M—↠N

len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ ∎) = 0
len (_ —→⟨ x ⟩ red) = suc (len red)

value-irreducible : ∀ {V M : Term} → Value V → ¬ (V —→ M)
value-irreducible v V—→M = nope V—→M v
   where
   nope : ∀ {V M : Term} → V —→ M → Value V → ⊥
   nope (ξξ (□· M) () x₁ V→M) (ƛ̬ N)
   nope (ξξ (v ·□) () x₁ V→M) (ƛ̬ N)
   nope (ξξ □⟨ x₂ ⇒ x₃ ⟩ () x₁ V→M) (ƛ̬ N)
   nope (ξξ-blame (□· M) ()) (ƛ̬ N)
   nope (ξξ-blame (v ·□) ()) (ƛ̬ N)
   nope (ξξ-blame □⟨ x₁ ⇒ x₂ ⟩ ()) (ƛ̬ N)
   nope (ξξ (□· M) () x₁ V→M) ($̬ k)
   nope (ξξ (v ·□) () x₁ V→M) ($̬ k)
   nope (ξξ □⟨ x₂ ⇒ x₃ ⟩ () x₁ V→M) ($̬ k)
   nope (ξξ-blame (□· M) ()) ($̬ k)
   nope (ξξ-blame (v ·□) ()) ($̬ k)
   nope (ξξ-blame □⟨ x₁ ⇒ x₂ ⟩ ()) ($̬ k)
   nope (ξ □⟨ x₂ ⇒ .★ ⟩ V→M) (v 〈 g 〉) = nope V→M v
   nope (ξ-blame □⟨ x₁ ⇒ .★ ⟩) (() 〈 g 〉)
   nope (expand v′ AG ngA) (v 〈 g 〉) = ⊥-elim (ngA g)

value—↠ : ∀{V N : Term}
    → Value V
    → V —↠ N
    → N ≡ V
value—↠ v (_ ∎) = refl
value—↠ v (_ —→⟨ V—→M ⟩ M—↠N) = ⊥-elim (value-irreducible v V—→M)

app-multi-inv : ∀{L M N}
  → (r1 : L · M —↠ N)
  → (∃[ L′ ] (Σ[ r2 ∈ (L —↠ L′) ] (N ≡ L′ · M × len r1 ≡ len r2)))
    ⊎ (∃[ V ] ∃[ M′ ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ M′) ]
        (N ≡ V · M′ × len r1 ≡ len r2 + len r3)))
    ⊎ (∃[ V ] ∃[ W ] Σ[ r2 ∈ (L —↠ V) ] (Value V × Σ[ r3 ∈ (M —↠ W) ]
        (Value W × Σ[ r4 ∈ (V · W —↠ N) ] len r1 ≡ len r2 + len r3 + len r4)))
app-multi-inv = {!!}

{- Logical Relation for Type Safety -}

ValPred : Set₁
ValPred = {V : Term} → Value V → Set

ExpPred : Set₁
ExpPred = Term → Set

SafePred : Set₁
SafePred = (A : Type) → ValPred × ExpPred

Safe-step : (n : ℕ) → <-Rec (λ i → SafePred) n → SafePred
Safe-step zero rec A = (λ v → ⊤) , (λ M → ⊤)
Safe-step (suc n) rec A = 𝕍 A , 𝔼
  where
  𝕍 : Type → ValPred
  𝔼 : ExpPred
  
  𝕍 ★ (ƛ̬ N) = ⊥
  𝕍 ★ ($̬ k) = ⊥
  𝕍 ★ {(V ⟨ G ⇒ ★ ⟩)} (v 〈 g 〉) = (proj₁ (rec n (n<1+n n) G)) v
  𝕍 ($ₜ ι) (ƛ̬ N) = ⊥
  𝕍 ($ₜ ι) ($̬ k) = ⊤
  𝕍 ($ₜ ι) (v 〈 g 〉) = ⊥
  𝕍 (A ⇒ B) {.(ƛ N)} (ƛ̬ N) =
     ∀ {V} (v : Value V) (j : ℕ) → (lt : j < n)
       → (proj₁ (rec j (≤-step lt) A)) v
       → (proj₂ (rec j (≤-step lt) B)) (N [ V ])
  𝕍 (A ⇒ B) ($̬ k) = ⊥
  𝕍 (A ⇒ B) (v 〈 g 〉) = ⊥

  {- the following is an experiment in that it does not relate the step
     index n to the number of reduction steps -}
  𝔼 M = ∀ N → (M→N : M —↠ N)
             → (Σ[ v ∈ Value N ] (proj₁ (rec n (s≤s ≤-refl) A)) v)
               ⊎ (∃[ N′ ] (N —→ N′))

abstract
  Safe : ℕ → SafePred
  Safe = <-rec (λ i → SafePred) Safe-step

𝓥⟦_⟧ : (A : Type) → {V : Term} → Value V → ℕ → Set
𝓥⟦ A ⟧ v k = proj₁ (Safe k A) v

𝓔⟦_⟧ : Type → Term → ℕ → Set
𝓔⟦ A ⟧ M k = proj₂ (Safe k A) M

postulate
  Safe-step-ext : (x : ℕ) → ∀ {IH IH′}
      → (∀{y} (y<x : y < x) → IH y y<x ≡ IH′ y y<x)
      → Safe-step x IH ≡ Safe-step x IH′

abstract
  unfold-Safe : ∀ n → Safe n ≡ Safe-step n (λ n′ _ → Safe n′)
  unfold-Safe n = FixPoint.unfold-wfRec <-wellFounded (λ i → SafePred)
                     Safe-step Safe-step-ext {n}

{- Equations of the logical relation -}

V-zero : ∀{A}{V} (v : Value V) → 𝓥⟦ A ⟧ v 0 ≡ ⊤
V-zero v rewrite unfold-Safe 0 = refl

V-base : ∀{n}{ι}{k : rep ι} → 𝓥⟦ $ₜ ι ⟧ ($̬ k)  (suc n) ≡ ⊤
V-base {n} rewrite unfold-Safe (suc n) = refl

V-dyn : ∀{n}{G}{V}{v : Value V}{g}
 → 𝓥⟦ ★ ⟧ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) (suc n) ≡ 𝓥⟦ G ⟧ v n
V-dyn {n} rewrite unfold-Safe (suc n) | sym (unfold-Safe n) = refl

V-fun : ∀{n}{A B}{N}
  → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ N) (suc n) ≡ ∀ {V} (v : Value V) (j : ℕ) → (lt : j < n)
                                → 𝓥⟦ A ⟧ v j → 𝓔⟦ B ⟧ (N [ V ]) j
V-fun {n} rewrite unfold-Safe (suc n) | sym (unfold-Safe n) = refl

E-zero : (A : Type)
   → (M : Term)
   → 𝓔⟦ A ⟧ M 0 ≡ ⊤
E-zero A M rewrite unfold-Safe 0 = refl

E-suc : (A : Type)
   → (M : Term)
   → (k : ℕ)
   → 𝓔⟦ A ⟧ M (suc k) ≡
       ∀ N → (M→N : M —↠ N)
             → (Σ[ v ∈ Value N ] 𝓥⟦ A ⟧ v k)
               ⊎ (∃[ N′ ] (N —→ N′))   
E-suc A M k rewrite unfold-Safe (suc k) = refl

{- Type Safety -}

ValSubst : Set
ValSubst = Σ[ σ ∈ Subst ] (∀ x → Value (σ x))

inc : ValSubst → ValSubst
inc σ = (λ x → proj₁ σ (suc x)) , (λ x → proj₂ σ (suc x))

𝓖⟦_⟧ : (Γ : List Type) → ValSubst → ℕ → Set
𝓖⟦ [] ⟧ σ k = ⊤
𝓖⟦ A ∷ Γ ⟧ σ k = 𝓖⟦ Γ ⟧ (inc σ) k × 𝓥⟦ A ⟧ (proj₂ σ 0) k

lemma-𝓖 : (Γ : List Type) → (γ : ValSubst) → (k : ℕ) → 𝓖⟦ Γ ⟧ γ k
  → ∀ {A}{y} → (∋y : Γ ∋ y ⦂ A)
  → 𝓥⟦ A ⟧ (proj₂ γ y) k
lemma-𝓖 [] γ k 𝓖γ ()
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {zero} refl = 𝓥γ0
lemma-𝓖 (A ∷ Γ) γ k (𝓖γ , 𝓥γ0) {B} {suc y} ∋y =
  lemma-𝓖 Γ (inc γ) k 𝓖γ ∋y

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓔⟦ A ⟧ (⟪ proj₁ γ ⟫ M) k

_⊨ⱽ_⦂_ : List Type → {V : Term} → Value V → Type → Set
Γ ⊨ⱽ v ⦂ A = ∀ k (γ : ValSubst) → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⟧ (sub-val (proj₁ γ) v) k

mono-SafeVal : ∀ j k A {V} (v : Value V)
   → j ≤′ k
   → 𝓥⟦ A ⟧ v k
   → 𝓥⟦ A ⟧ v j
mono-SafeVal j .j A v ≤′-refl Vv = Vv
mono-SafeVal zero (suc k) A (ƛ̬ N) (≤′-step lt) Vv
    rewrite unfold-Safe 0 = tt
mono-SafeVal (suc j) (suc k) ★ (ƛ̬ N) (≤′-step lt) Vv
    rewrite unfold-Safe (suc k)
    with Vv
... | ()
mono-SafeVal (suc j) (suc k) ($ₜ ι) (ƛ̬ N) (≤′-step lt) Vv
    rewrite unfold-Safe (suc k)
    with Vv
... | ()
mono-SafeVal (suc j) (suc k) (A ⇒ B) {ƛ N} (ƛ̬ _) (≤′-step lt) Vv
    rewrite unfold-Safe (suc j) | unfold-Safe (suc k) = G
    where
    G : ∀ {V} (v : Value V) (j₁ : ℕ) (lt₁ : suc j₁ ≤ j)
        → proj₁ (Safe j₁ A) v → proj₂ (Safe j₁ B) (⟪ V • id ⟫ N)
    G {V} v j′ j′≤j Vvj′ =
        Vv v j′ (≤-trans j′≤j (≤-trans (n≤1+n j) (≤′⇒≤ lt))) Vvj′ 
mono-SafeVal zero (suc k) A ($̬ c) (≤′-step lt) Vv
    rewrite unfold-Safe 0 = tt
mono-SafeVal (suc j) (suc k) ★ ($̬ c) (≤′-step lt) Vv 
    rewrite unfold-Safe (suc k)
    with Vv
... | ()
mono-SafeVal (suc j) (suc k) ($ₜ ι) ($̬ c) (≤′-step lt) Vv
    rewrite unfold-Safe (suc j) = tt
mono-SafeVal (suc j) (suc k) (A ⇒ B) ($̬ c) (≤′-step lt) Vv
    rewrite unfold-Safe (suc k)
    with Vv
... | ()
mono-SafeVal zero (suc k) A (v 〈 g 〉) (≤′-step lt) Vv
    rewrite unfold-Safe 0 = tt
mono-SafeVal (suc j) (suc k) ★ {V ⟨ G ⇒ ★ ⟩} (v 〈 g 〉) (≤′-step lt) Vv
    rewrite unfold-Safe (suc j) | unfold-Safe (suc k) =
    mono-SafeVal j k G v (≤′-trans (≤⇒≤′ (n≤1+n j)) lt) Vv
mono-SafeVal (suc j) (suc k) ($ₜ ι) (v 〈 g 〉) (≤′-step lt) Vv
    rewrite unfold-Safe (suc k)
    with Vv
... | ()
mono-SafeVal (suc j) (suc k) (A ⇒ B) (v 〈 g 〉) (≤′-step lt) Vv
    rewrite unfold-Safe (suc k)
    with Vv
... | ()

mono-SafeExp : ∀ j k A (M : Term)
   → j ≤′ k
   → 𝓔⟦ A ⟧ M k
   → 𝓔⟦ A ⟧ M j
mono-SafeExp j .j A M ≤′-refl EM = EM
mono-SafeExp zero (suc k) A M (≤′-step j≤k) EM rewrite unfold-Safe 0 = tt
mono-SafeExp (suc j) (suc k) A M (≤′-step j≤k) EM
  rewrite unfold-Safe (suc j) | unfold-Safe (suc k) = G
  where
  G : (N : Term) → M —↠ N →
      Data.Product.Σ (Value N) (proj₁ (Safe j A))
      ⊎ Data.Product.Σ Term (_—→_ N)
  G N M→N
      with EM N M→N  
  ... | inj₂ (N′ , N—→N′) = inj₂ (N′ , N—→N′)
  ... | inj₁ (v , Vk) =
        inj₁ (v , mono-SafeVal j k A v (≤′-trans (≤⇒≤′ (n≤1+n j)) j≤k) Vk)

mono-SafeEnv : ∀ j k {Γ} (γ : ValSubst)
   → j ≤′ k
   → 𝓖⟦ Γ ⟧ γ k
   → 𝓖⟦ Γ ⟧ γ j
mono-SafeEnv = {!!}

Val⇒Exp : ∀{A}{V : Term}{v : Value V} (k : ℕ)
   → 𝓥⟦ A ⟧ v k
   → 𝓔⟦ A ⟧ V k
Val⇒Exp zero Vv rewrite unfold-Safe 0 = tt
Val⇒Exp {A}{V}{v} (suc k) Vv rewrite E-suc A V k =  G
  where G : (N : Term) → V —↠ N →
                Data.Product.Σ (Value N) (proj₁ (Safe k A)) ⊎
                Data.Product.Σ Term (_—→_ N)
        G N V→N rewrite value—↠ v V→N =
          inj₁ (v , mono-SafeVal k (suc k) A v (≤′-step ≤′-refl) Vv)

{-# REWRITE sub-var #-}

fundamental : ∀ {Γ A} → (M : Term)
  → (Γ ⊢ M ⦂ A)
    -----------
  → (Γ ⊨ M ⦂ A)
fundamentalⱽ : ∀ {Γ W A} → (w : Value W)
  → (Γ ⊢ W ⦂ A)
    ------------
  → (Γ ⊨ⱽ w ⦂ A)

fundamental {Γ}{A} (` x) (⊢` ∋x) k γ 𝓖Γγk  =
  let Vγx = lemma-𝓖 Γ γ k 𝓖Γγk ∋x in
  Val⇒Exp {A}{⟪ proj₁ γ ⟫ (` x)} k Vγx
fundamental ($ c) (⊢$ ι) k γ 𝓖Γγk = Val⇒Exp {v = $̬ c} k (Vc k)
  where
  Vc : ∀ k → 𝓥⟦ $ₜ ι ⟧ ($̬ c) k
  Vc zero rewrite V-zero {$ₜ ι} ($̬ c) = tt
  Vc (suc k) rewrite V-base {k}{ι}{c} = tt
fundamental (L · M) (⊢· {A = A}{B} ⊢L ⊢M) 0 γ 𝓖Γγk
    rewrite E-zero B (⟪ proj₁ γ ⟫ (L · M)) = tt
fundamental (L · M) (⊢· {A = A}{B} ⊢L ⊢M) (suc k) γ 𝓖Γγk
  rewrite E-suc B (⟪ proj₁ γ ⟫ (L · M)) k = G
  where
  G : (N : Term) → ⟪ proj₁ γ ⟫ L · ⟪ proj₁ γ ⟫ M —↠ N →
       Data.Product.Σ (Value N) (proj₁ (Safe k B)) ⊎
       Data.Product.Σ Term (_—→_ N)
  G N γLM—↠N
      with fundamental L ⊢L (suc k) γ 𝓖Γγk
  ... | 𝓔γL rewrite E-suc (A ⇒ B) (⟪ proj₁ γ ⟫ L) k 
      with fundamental M ⊢M (suc k) γ 𝓖Γγk
  ... | 𝓔γM rewrite E-suc A (⟪ proj₁ γ ⟫ M) k
      with app-multi-inv γLM—↠N
  ... | inj₂ (inj₁ (V , M′ , γL→V , v , γM→M′ , refl , eq)) = {!!}
  G N γLM—↠N | 𝓔γL | 𝓔γM | inj₂ (inj₂ (V , W , γL→V , v , γM→W , w , VW→N , eq)) = {!!}
  G N γLM—↠N | 𝓔γL | 𝓔γM | inj₁ (L′ , L→L′ , refl , eq)
      with 𝓔γL L′ L→L′
  ... | inj₂ (L″ , L′→L″) =
        inj₂ ((L″ · ⟪ proj₁ γ ⟫ M) , (ξ (□· ⟪ proj₁ γ ⟫ M) L′→L″))
  ... | inj₁ (vL′ , VL′) = {!!}
fundamental {Γ}{A = A ⇒ B}(ƛ N) (⊢ƛ ⊢N) k γ 𝓖Γγk =
  Val⇒Exp {V = ⟪ proj₁ γ ⟫ (ƛ N)}{ƛ̬ ⟪ ext (proj₁ γ) ⟫ N} k (G k 𝓖Γγk)
  where
    G : ∀ k → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ ⟪ ext (proj₁ γ) ⟫ N) k
    G zero 𝓖Γγk rewrite V-zero {A ⇒ B} (ƛ̬ ⟪ ext (proj₁ γ) ⟫ N) = tt
    G (suc k) 𝓖Γγk rewrite V-fun {k}{A}{B}{⟪ ext (proj₁ γ) ⟫ N} = H
      where
      H : ∀ {V} (v : Value V) (j : ℕ) → suc j ≤ k
        → 𝓥⟦ A ⟧ v j
        → 𝓔⟦ B ⟧ ((⟪ ext (proj₁ γ) ⟫ N) [ V ]) j
      H {V} v j lt Vvj =
        fundamental N ⊢N j γ′ (mono-SafeEnv j (suc k) _ lt2 𝓖Γγk , Vvj)
        where γ′ = (V • proj₁ γ , λ { zero → v ; (suc x) → proj₂ γ x})
              lt2 = (≤⇒≤′ (≤-trans (n≤1+n j) (≤-trans lt (n≤1+n k))))
fundamental (M ⟨ A ⇒ B ⟩) (⊢⟨⇒⟩ ⊢M) = {!!}
fundamental blame ⊢blame = {!!}

fundamentalⱽ w ⊢W = {!!}
