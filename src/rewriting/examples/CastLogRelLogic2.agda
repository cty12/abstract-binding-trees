{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastLogRelLogic2 where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import Structures using (extensionality)
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic2

pre-𝓥 : Type → Term → Fun (Type × Term) ⊤ Wellfounded
pre-𝓥 ★ (op-inject{G} g ⦅ cons (ast V) nil ⦆) =
    (Value V)ᶠ ×ᶠ ▷ᶠ (recur (G , V))
pre-𝓥 ($ₜ ι) (op-lit {ι′} c ⦅ nil ⦆) = (ι ≡ ι′)ᶠ
pre-𝓥 (A ⇒ B) (ƛ N) =
    ∀ᶠ{Term} λ W → ▷ᶠ (recur (A , W)) →ᶠ (irred W)ᶠ →ᶠ
                   ▷ᶠ (recur (A , N [ W ]))

-- bogus cases for ★
pre-𝓥 ★ (` x) = (⊥) ᶠ
pre-𝓥 ★ ($ c) = (⊥) ᶠ
pre-𝓥 ★ (ƛ N) = (⊥) ᶠ
pre-𝓥 ★ (L · M) = (⊥) ᶠ
pre-𝓥 ★ (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝓥 ★ blame = (⊥) ᶠ

-- bogus cases for ι
pre-𝓥 ($ₜ ι) (` x) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (ƛ N) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (L · M) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (M ⟨ g !⟩) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝓥 ($ₜ ι) blame = (⊥) ᶠ

-- bogus cases for A ⇒ B
pre-𝓥 (A ⇒ B) (` x) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) ($ c) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) (L · M) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) (M ⟨ g !⟩) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) (M ⟨ h ?⟩) = (⊥) ᶠ
pre-𝓥 (A ⇒ B) blame = (⊥) ᶠ

-- Type Safety = Progress & Preservation
pre-𝓔 : Type × Term → Fun (Type × Term) ⊤ Wellfounded
pre-𝓔 (A , M) = (pre-𝓥 A M ⊎ᶠ (red M)ᶠ)
                 ×ᶠ ∀ᶠ{Term} λ N → ((M —→ N) ᶠ) →ᶠ ▷ᶠ (recur (A , N))

𝓔ᶠ : Fun (Type × Term) (Type × Term) Wellfounded
𝓔ᶠ = flipᶠ pre-𝓔 tt

𝓔⟦_⟧ : (A : Type) → Term → Setₒ
𝓔⟦ A ⟧ V = #(μᵖ 𝓔ᶠ) (A , V)

𝓔-fixpointₚ : #(μᵖ 𝓔ᶠ) ≡ₚ #((fun 𝓔ᶠ) (μᵖ 𝓔ᶠ))
𝓔-fixpointₚ = fixpoint 𝓔ᶠ

𝓔-fixpointₒ : ∀ A M → #(μᵖ 𝓔ᶠ) (A , M) ≡ₒ #((fun 𝓔ᶠ) (μᵖ 𝓔ᶠ)) (A , M)
𝓔-fixpointₒ A M = fixpoint 𝓔ᶠ (A , M)

𝓥⟦_⟧ : (A : Type) → Term → Setₒ
𝓥⟦ A ⟧ V = (λ k → # (fun (pre-𝓥 A V) (μᵖ 𝓔ᶠ)) tt k)

𝓔-def : ∀{A}{M}
  → 𝓔⟦ A ⟧ M ≡ₒ (𝓥⟦ A ⟧ M ⊎ₒ (red M)ₒ)
                ×ₒ ∀ₒ λ N → ((M —→ N) ₒ) →ₒ ▷ₒ 𝓔⟦ A ⟧ N
𝓔-def {A}{M} =
  𝓔⟦ A ⟧ M                                                    ≡ₒ⟨ ≡ₒ-refl refl ⟩
  #(μᵖ 𝓔ᶠ) (A , M)                                         ≡ₒ⟨ 𝓔-fixpointₒ A M ⟩
  #((fun 𝓔ᶠ) (μᵖ 𝓔ᶠ)) (A , M)                                 ≡ₒ⟨ ≡ₒ-refl refl ⟩
  ((𝓥⟦ A ⟧ M ⊎ₒ (red M)ₒ)
    ×ₒ ∀ₒ λ N → ((M —→ N) ₒ) →ₒ ▷ₒ 𝓔⟦ A ⟧ N)
  QEDₒ


-- V-base-intro : ∀{n}{ι}{c : rep ι}
--    → 𝓥⟦ $ₜ ι ⟧ ($ c) n
-- V-base-intro {zero} = tt , inj₁ (tt , tt) , λ { a .zero z≤n _ k ()}
-- V-base-intro {suc n}{ι}{c} =
--    let ir = value-irred ($̬ c) in
--    ir , (inj₁ (ir , refl)) ,
--    λ { a .(suc _) (s≤s x) rd k _ → ⊥-elim (ir (_ , rd))}

-- V-base-elim : ∀{n}{ι}{ι′}{c : rep ι′}
--    → 𝓥⟦ $ₜ ι ⟧ ($ c) (suc n)
--    → (ι ≡ ι′)
-- V-base-elim {n} (ir , inj₁ (_ , refl) , pres) = refl
-- V-base-elim {n} (ir , inj₂ rd , pres) = ⊥-elim (ir rd)


-- V-dyn-intro : ∀{G}{V}{g : Ground G}{n}
--    → Value V
--    → 𝓥⟦ G ⟧ V n
--    → 𝓥⟦ ★ ⟧ (V ⟨ g !⟩) (suc n)
-- V-dyn-intro {G}{V}{g}{n} v (irV , 𝓔V) =
--    let unroll = proj₁ (𝓔-fixpointₚ (G , V) n) in
--    let x = unroll 𝓔V in
--    let P = apply (fun (pre-𝓔 (G , V)) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt in
--    {-
--    # (fun (pre-𝓔 (G , V)) (iter n (flip pre-𝓔 tt) ⊤ᵖ)) tt)
--    -}
--    (value-irred (v 〈 g 〉)) , {!!}
--    --(inj₁ (v , ▷ᵒ-intro{n}{P} {!!}))
