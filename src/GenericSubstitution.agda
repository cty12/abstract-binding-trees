{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)

module GenericSubstitution where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Var

infixr 6 _•_

data Substitution : (V : Set) → Set where
  ↑ : (k : ℕ) → ∀{V} → Substitution V
  _•_ : ∀{V} → V → Substitution V → Substitution V

id : ∀ {V} → Substitution V
id = ↑ 0

g-map-sub : ∀{V W} → (V → W) → Substitution V → Substitution W
g-map-sub f (↑ k) = ↑ k
g-map-sub f (v • σ) = f v • g-map-sub f σ

g-map-sub-id : ∀{V} (σ : Substitution V) → g-map-sub (λ x → x) σ ≡ σ
g-map-sub-id (↑ k) = refl
g-map-sub-id (v • σ) = cong₂ _•_ refl (g-map-sub-id σ)
{-# REWRITE g-map-sub-id #-}

g-drop : ∀{V} → (k : ℕ) → Substitution V → Substitution V
g-drop k (↑ k') = ↑ (k + k')
g-drop zero (v • σ) = v • σ
g-drop (suc k) (v • σ) = g-drop k σ

g-map-sub-drop : ∀ {V W} σ f k
   → g-map-sub {V}{W} f (g-drop k σ) ≡ g-drop k (g-map-sub f σ)
g-map-sub-drop (↑ k₁) f k = refl
g-map-sub-drop (v • σ) f zero = refl
g-map-sub-drop (v • σ) f (suc k) = g-map-sub-drop σ f k

g-drop-0 : ∀ {V} σ → g-drop {V} 0 σ ≡ σ
g-drop-0 (↑ k) = refl
g-drop-0 (v • σ) = refl
{-# REWRITE g-drop-0 #-}
  
g-drop-drop : ∀ {V} k k' σ → g-drop {V} (k + k') σ ≡ g-drop k (g-drop k' σ)
g-drop-drop k k' (↑ k₁) rewrite +-assoc k k' k₁ = refl
g-drop-drop zero k' (v • σ) = refl
g-drop-drop (suc k) zero (v • σ) rewrite +-comm k 0 = refl
g-drop-drop (suc k) (suc k') (v • σ)
    with g-drop-drop (suc k) k' σ
... | IH rewrite +-comm k (suc k') | +-comm k k' = IH

record Substable (V : Set) : Set where
  field var→val : Var → V
        shift : V → V
        var→val-suc-shift : ∀{x} → var→val (suc x) ≡ shift (var→val x)

module GenericSubst {V} (S : Substable V) where
  open Substable S

  ⧼_⧽ : Substitution V → Var → V
  ⧼ ↑ k ⧽ x = var→val (k + x)
  ⧼ y • σ ⧽ 0 = y
  ⧼ y • σ ⧽ (suc x) = ⧼ σ ⧽ x

  g-inc : Substitution V → Substitution V
  g-inc (↑ k) = ↑ (suc k)
  g-inc (v • ρ) = shift v • g-inc ρ

  g-extend : V → Substitution V → Substitution V
  g-extend v σ = v • g-inc σ
  
  g-ext : Substitution V → Substitution V
  g-ext σ = g-extend (var→val 0) σ

  shifts : ℕ → V → V
  shifts zero v = v
  shifts (suc k) v = shift (shifts k v) 

  g-drop-add : ∀{x : Var} (k : ℕ) (σ : Substitution V)
           → ⧼ g-drop k σ ⧽ x ≡ ⧼ σ ⧽ (k + x)
  g-drop-add {x} k (↑ k') rewrite +-comm k k' | +-assoc k' k x = refl
  g-drop-add {x} zero (v • σ) = refl
  g-drop-add {x} (suc k) (v • σ) = g-drop-add k σ

  g-drop-inc : ∀ k σ → g-drop k (g-inc σ) ≡ g-inc (g-drop k σ)
  g-drop-inc k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  g-drop-inc zero (v • σ) = refl
  g-drop-inc (suc k) (v • σ) = g-drop-inc k σ

  g-Z-shift : ∀ x → ⧼ var→val 0 • ↑ 1 ⧽ x ≡ var→val x
  g-Z-shift 0 = refl
  g-Z-shift (suc x) = refl

  g-inc-shift : ∀ ρ x → ⧼ g-inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
  g-inc-shift (↑ k) x rewrite +-comm k x = var→val-suc-shift
  g-inc-shift (y • ρ) zero = refl
  g-inc-shift (y • ρ) (suc x) = g-inc-shift ρ x

  g-ext-cong : ∀ {σ₁ σ₂} → ((x : ℕ) → ⧼ σ₁ ⧽ x ≡ ⧼ σ₂ ⧽ x)
    → (x : ℕ) → ⧼ g-ext σ₁ ⧽ x ≡ ⧼ g-ext σ₂ ⧽ x
  g-ext-cong {σ₁} {σ₂} f zero = refl
  g-ext-cong {σ₁} {σ₂} f (suc x)
      rewrite g-inc-shift σ₁ x | g-inc-shift σ₂ x | f x = refl

  g-drop-ext : ∀ k ρ → g-drop (suc k) (g-ext ρ) ≡ g-inc (g-drop k ρ)
  g-drop-ext k (↑ k₁) rewrite +-comm k (suc k₁) | +-comm k₁ k = refl
  g-drop-ext zero (x • ρ) = refl
  g-drop-ext (suc k) (x • ρ) = g-drop-inc k ρ

  data Shift : ℕ → Substitution V → Set where
    shift-up : ∀{k} → Shift k (↑ k)
    shift-• : ∀{k σ v} → Shift (suc k) σ → v ≡ shifts k (var→val 0)
       → Shift k (v • σ)

  g-inc-Shift : ∀ {k σ} → Shift k σ → Shift (suc k) (g-inc σ)
  g-inc-Shift shift-up = shift-up
  g-inc-Shift (shift-• kσ refl) = shift-• (g-inc-Shift kσ) refl

  shifts0 : ∀ k → shifts k (var→val 0) ≡ var→val k
  shifts0 zero = refl
  shifts0 (suc k) rewrite shifts0 k | var→val-suc-shift {k} = refl

  g-Shift-var : ∀ {σ}{k} (x : Var) → Shift k σ → ⧼ σ ⧽ x ≡ var→val (k + x)
  g-Shift-var {.(↑ k)}{k} x shift-up = refl
  g-Shift-var {v • _}{k} zero (shift-• σk refl)
      rewrite +-comm k 0 = shifts0 k
  g-Shift-var {v • σ}{k} (suc x) (shift-• σk refl) rewrite +-suc k x =
      g-Shift-var {σ}{suc k} x σk

  data ShftAbv : ℕ → ℕ → ℕ → Substitution V → Set where
    sha-0 : ∀{k k′ σ}
       → Shift k σ
       → ShftAbv k 0 k′ σ
    sha-suc : ∀{k c k′ σ v}
       → ShftAbv (suc k) c (suc k′) σ
       → v ≡ shifts k′ (var→val 0)
       → ShftAbv k (suc c) k′ (v • σ)

  g-inc-ShftAbv : ∀{k c k′ σ}
     → ShftAbv k c k′ σ
     → ShftAbv (suc k) c (suc k′) (g-inc σ)
  g-inc-ShftAbv {k} {.0} {k′} {σ} (sha-0 σk) = sha-0 (g-inc-Shift σk)
  g-inc-ShftAbv {k} {.(suc _)} {k′} {.(_ • _)} (sha-suc σkc refl) =
     sha-suc (g-inc-ShftAbv σkc) refl

  g-ext-ShftAbv : ∀ {k c σ}
     → ShftAbv k c 0 σ
     → ShftAbv k (suc c) 0 (g-ext σ)
  g-ext-ShftAbv {k} {.0} {σ} (sha-0 σk) = sha-suc (sha-0 (g-inc-Shift σk)) refl
  g-ext-ShftAbv {k} {.(suc _)} {.(_ • _)} (sha-suc σk refl) =
      sha-suc (sha-suc (g-inc-ShftAbv σk) refl) refl

  g-ShftAbv→Shift : ∀ {k c σ} → ShftAbv k c k σ → Shift k σ
  g-ShftAbv→Shift {k} {.0} (sha-0 σk) = σk
  g-ShftAbv→Shift {k} {suc c} {v • σ} (sha-suc σkc refl) =
      shift-• (g-ShftAbv→Shift{suc k}{c}{σ} σkc) refl

module Relate {V₁}{V₂} (S₁ : Substable V₁) (S₂ : Substable V₂)
    (_∼_ : V₁ → V₂ → Set)
    (var→val∼ : ∀ x → Substable.var→val S₁ x ∼ Substable.var→val S₂ x)
    (shift∼ : ∀{v₁ v₂}→ v₁ ∼ v₂ → Substable.shift S₁ v₁ ∼ Substable.shift S₂ v₂)
    where
    module G₁ = GenericSubst S₁
    module G₂ = GenericSubst S₂

    data _≊_ : Substitution V₁ → Substitution V₂ → Set where
       r-up : ∀{k} → (↑ k) ≊ (↑ k)
       r-cons : ∀{v₁ σ₁ v₂ σ₂}
          → v₁ ∼ v₂  →   σ₁ ≊ σ₂
          → (v₁ • σ₁) ≊ (v₂ • σ₂)

    g-inc-≊ : ∀ {σ₁ σ₂} → σ₁ ≊ σ₂ → G₁.g-inc σ₁ ≊ G₂.g-inc σ₂
    g-inc-≊ {.(↑ _)} {.(↑ _)} r-up = r-up
    g-inc-≊ {.(_ • _)} {.(_ • _)} (r-cons v₁~v₂ σ₁≊σ₂) =
        r-cons (shift∼ v₁~v₂ ) (g-inc-≊ σ₁≊σ₂)

    g-ext-≊ : ∀ {σ₁ σ₂} → σ₁ ≊ σ₂ → G₁.g-ext σ₁ ≊ G₂.g-ext σ₂
    g-ext-≊ {σ₁}{σ₂} σ₁≊σ₂ = r-cons (var→val∼ 0) (g-inc-≊ σ₁≊σ₂)

    g-lookup : ∀ {σ₁ σ₂} x → σ₁ ≊ σ₂ → G₁.⧼_⧽ σ₁ x ∼ G₂.⧼_⧽ σ₂ x
    g-lookup x (r-up{k}) = var→val∼ (k + x)
    g-lookup zero (r-cons v₁∼v₂ σ₁≊σ₂) = v₁∼v₂
    g-lookup (suc x) (r-cons v₁∼v₂ σ₁≊σ₂) = g-lookup x σ₁≊σ₂