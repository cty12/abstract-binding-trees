{-# OPTIONS --rewriting #-}
module rewriting.examples.CastSafeLogic where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ᵖ; tt to ttᵖ)
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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic
open import rewriting.examples.CastDeterministic
open import rewriting.examples.CastLogRelLogic

{-# REWRITE sub-var #-}

compatible-blame : ∀{Γ}{A}
     -------------------
   → Γ ⊨ blame ⦂ A
compatible-blame {Γ}{A} γ = ℰ-blame

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ =
     let ⊢𝒱γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ x)
         ⊢𝒱γx = lookup-𝓖 Γ γ ∋x in
     𝒱⇒ℰ ⊢𝒱γx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} γ =
     let ⊢𝒱n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝒱n = ⊢ᵒ-intro λ { zero x → tt ; (suc k) x → refl} in
     𝒱⇒ℰ ⊢𝒱n

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} γ =
     let ⊢𝒱b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝒱b = ⊢ᵒ-intro λ { zero x → tt ; (suc k) x → refl} in
     𝒱⇒ℰ ⊢𝒱b

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢ℰLM
 where
 ⊢ℰL : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⇒ B ⟧ (⟪ γ ⟫ L)
 ⊢ℰL = ⊨L γ

 ⊢ℰM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
 ⊢ℰM = ⊨M γ

 ⊢ℰLM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ B ⟧ (⟪ γ ⟫ (L · M))
 ⊢ℰLM = ℰ-frame {F = □· (⟪ γ ⟫ M)} ⊢ℰL (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVM))
  where
  𝓟₁ = λ V → 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVM : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢ℰVM {V} = sucP⊢ᵒQ λ 𝒱Vsn →
       let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
       let 𝓟₁⊢ℰM : 𝓟₁ V ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
           𝓟₁⊢ℰM = Sᵒ (Sᵒ ⊢ℰM) in
       ℰ-frame {F = v ·□} 𝓟₁⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVW))
   where
   𝓟₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ
                 ∷ 𝓖⟦ Γ ⟧ γ
   ⊢ℰVW : ∀{V W} → 𝓟₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
   ⊢ℰVW {V}{W} =
     let ⊢𝒱V : 𝓟₂ V W ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
         ⊢𝒱V = Sᵒ (Sᵒ Zᵒ) in
     let ⊢𝒱W : 𝓟₂ V W ⊢ᵒ 𝒱⟦ A ⟧ W
         ⊢𝒱W = Zᵒ in
     ⊢ᵒ-sucP ⊢𝒱W λ 𝒱Wsn →
     let w = 𝒱⇒Value A W 𝒱Wsn in
     V-fun-elim ⊢𝒱V λ {N′ refl 𝒱W→ℰNW →
     let prog : 𝓟₂ (ƛ N′) W ⊢ᵒ progress B (ƛ N′ · W)
         prog = (inj₂ᵒ (inj₁ᵒ (⊢ᵒ-Sᵒ-intro (_ , (β w))))) in
     let pres : 𝓟₂ (ƛ N′) W ⊢ᵒ preservation B (ƛ N′ · W)
         pres = Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ {r →
                let ⊢▷ℰN′W = appᵒ 𝒱W→ℰNW (⊢ᵒ-mono ⊢𝒱W) in
                let eq = deterministic r (β w) in
                subst (λ N → 𝓟₂ (ƛ N′) W ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ N) (sym eq) ⊢▷ℰN′W}) in
     ℰ-intro prog pres
     }

compatible-lambda : ∀{Γ}{A}{B}{N}
   → (A ∷ Γ) ⊨ N ⦂ B
     -------------------
   → Γ ⊨ (ƛ N) ⦂ (A ⇒ B)
compatible-lambda {Γ}{A}{B}{N} ⊨N γ = ⊢ℰγλN
 where
 ⊢ℰγλN : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⇒ B ⟧ (ƛ (⟪ ext γ ⟫ N))
 ⊢ℰγλN =
   𝒱⇒ℰ (substᵒ (≡ᵒ-sym V-fun) (Λᵒ[ W ] →ᵒI ▷𝓔N[W]))
   where
   ▷𝓔N[W] : ∀{W} → ▷ᵒ 𝒱⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ ℰ⟦ B ⟧ ((⟪ ext γ ⟫ N) [ W ])
   ▷𝓔N[W] {W} =
     let ⊢𝒱W→ℰN[W] : 𝓖⟦ Γ ⟧ γ ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W) →ᵒ ▷ᵒ ℰ⟦ B ⟧ (⟪ W • γ ⟫ N))
         ⊢𝒱W→ℰN[W] = ▷→ (⊢ᵒ-mono (→ᵒI (⊨N (W • γ)))) in
     appᵒ (Sᵒ ⊢𝒱W→ℰN[W]) Zᵒ

compatible-inject : ∀{Γ}{G}{g}{M}
  → Γ ⊨ M ⦂ G
  → Γ ⊨ M ⟨ G , g !⟩ ⦂ ★
compatible-inject {Γ}{G}{g}{M} ⊨M γ = ℰMg!
 where
 ⊢ℰM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ G ⟧ (⟪ γ ⟫ M)
 ⊢ℰM = ⊨M γ
  
 ℰMg! : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ ★ ⟧ ((⟪ γ ⟫ M) ⟨ G , g !⟩)
 ℰMg! = ℰ-frame {F = □⟨ G , g !⟩} ⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVg!))
  where
  𝓟₁ = λ V → 𝒱⟦ G ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVg! : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ ★ ⟧ (V ⟨ G , g !⟩)
  ⊢ℰVg!{V} =
   ⊢ᵒ-sucP Zᵒ λ 𝒱Vsn →
   let v = 𝒱⇒Value G V 𝒱Vsn in
   𝒱⇒ℰ (substᵒ (≡ᵒ-sym V-dyn) (⊢ᵒ-Sᵒ-intro v ,ᵒ (⊢ᵒ-mono Zᵒ)))

red-inj-proj : ∀{G}{H}{g}{h}{W}
   → Value W
   → reducible ((W ⟨ G , g !⟩) ⟨ H , h ?⟩)
red-inj-proj {G} {H} {g} {h} {W} w
    with g ≡ᵍ h
... | yes refl = W , (collapse w g h refl)
... | no neq = blame , (collide w g h neq refl)

compatible-project : ∀{Γ}{H}{h : Ground H}{M}
  → Γ ⊨ M ⦂ ★
  → Γ ⊨ M ⟨ H , h ?⟩ ⦂ H
compatible-project {Γ}{H}{h}{M} ⊨M γ = ℰMh?
 where
 ⊢ℰM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ ★ ⟧ (⟪ γ ⟫ M)
 ⊢ℰM = ⊨M γ
  
 ℰMh? : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ H ⟧ ((⟪ γ ⟫ M) ⟨ H , h ?⟩)
 ℰMh? = ℰ-frame {F = □⟨ H , h ?⟩} ⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVh?))
  where
  𝓟₁ = λ V → 𝒱⟦ ★ ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVh? : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ H ⟧ (V ⟨ H , h ?⟩)
  ⊢ℰVh?{V} =
   let ⊢𝒱V : 𝓟₁ V ⊢ᵒ 𝒱⟦ ★ ⟧ V
       ⊢𝒱V = Zᵒ in
   V-dyn-elim ⊢𝒱V λ { W G g refl ⊢w×▷𝒱W →
   let ⊢w = proj₁ᵒ ⊢w×▷𝒱W in
   let ▷𝒱W = proj₂ᵒ ⊢w×▷𝒱W in
   ⊢ᵒ-sucP ⊢w λ{n} w →
   let prog : 𝓟₁ (W ⟨ G , g !⟩) ⊢ᵒ progress H ((W ⟨ G , g !⟩) ⟨ H , h ?⟩)
       prog = inj₂ᵒ (inj₁ᵒ (⊢ᵒ-Sᵒ-intro (red-inj-proj w))) in
   let pres : 𝓟₁ (W ⟨ G , g !⟩) ⊢ᵒ preservation H ((W ⟨ G , g !⟩) ⟨ H , h ?⟩)
       pres = Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ r → Goal r w ▷𝒱W) in
   ℰ-intro prog pres
   }
    where
    Goal : ∀{W}{G}{H}{g : Ground G}{h : Ground H}{N}
       → (W ⟨ G , g !⟩ ⟨ H , h ?⟩) —→ N
       → Value W
       → 𝓟₁ (W ⟨ G , g !⟩) ⊢ᵒ ▷ᵒ 𝒱⟦ G ⟧ W
       → 𝓟₁ (W ⟨ G , g !⟩) ⊢ᵒ ▷ᵒ ℰ⟦ H ⟧ N
    Goal{g = g} (ξξ □⟨ H , h ?⟩ refl refl r) w ▷𝒱W =
        ⊥-elim (value-irreducible (w 〈 g 〉) r)
    Goal {W} (ξξ-blame □⟨ H , h ?⟩ ())
    Goal {W}{G}{G}{g}{h}{W} (collapse{H} w′ g .h refl) w ▷𝒱W =
       ▷→▷ ▷𝒱W (→ᵒI (𝒱⇒ℰ Zᵒ))
    Goal {W} (collide x g h x₁ x₂) w ▷𝒱W = ⊢ᵒ-mono ℰ-blame

fundamental : ∀ {Γ A} → (M : Term)
  → Γ ⊢ M ⦂ A
    ----------
  → Γ ⊨ M ⦂ A
fundamental {Γ} {A} .(` _) (⊢` ∋x) =
    compatibility-var ∋x
fundamental {Γ} {.($ₜ ′ℕ)} .($ _) (⊢$ ′ℕ) =
    compatible-nat
fundamental {Γ} {.($ₜ ′𝔹)} .($ _) (⊢$ ′𝔹) =
    compatible-bool
fundamental {Γ} {A} (L · M) (⊢· ⊢L ⊢M) =
    compatible-app{L = L}{M} (fundamental L ⊢L) (fundamental M ⊢M)
fundamental {Γ} {.(_ ⇒ _)} (ƛ N) (⊢ƛ ⊢N) =
    compatible-lambda {N = N} (fundamental N ⊢N)
fundamental {Γ} {.★} (M ⟨ G , g !⟩) (⊢⟨!⟩ ⊢M g) =
    compatible-inject {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} (M ⟨ H , h ?⟩) (⊢⟨?⟩ ⊢M h) =
    compatible-project {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} .blame ⊢blame = compatible-blame

sem-type-safety : ∀ {A} → (M N : Term)
  → (r : M —↠ N)
  → # (ℰ⟦ A ⟧ M) (suc (len r))
    ---------------------------------------------
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
sem-type-safety {A} M .M (.M END) (inj₁ 𝒱M , presM) =
    inj₁ (𝒱⇒Value A M 𝒱M)
sem-type-safety {A} M .M (.M END) (inj₂ (inj₁ r) , presM) =
    inj₂ (inj₁ r)
sem-type-safety {A} M .M (.M END) (inj₂ (inj₂ isBlame) , presM) =
    inj₂ (inj₂ refl)
sem-type-safety {A} M N (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (_ , presM) =
    let ℰM′ : # (ℰ⟦ A ⟧ M′) (suc (len M′→N))
        ℰM′ = presM M′ (suc (suc (len M′→N))) ≤-refl M→M′ in
    sem-type-safety M′ N M′→N ℰM′

type-safety : ∀ {A} → (M N : Term)
  → [] ⊢ M ⦂ A
  → M —↠ N
    ---------------------------------------------
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
type-safety M N ⊢M M→N =
  let ℰM = ⊢ᵒ-elim ((fundamental M ⊢M) id) (suc (len M→N)) tt in
  sem-type-safety M N M→N ℰM 
