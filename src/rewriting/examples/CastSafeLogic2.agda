{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafeLogic2 where

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
open import rewriting.examples.StepIndexedLogic2
open import rewriting.examples.CastLogRelLogic2

{-# REWRITE sub-var #-}

compatible-blame : ∀{Γ}{A}
     -------------------
   → Γ ⊨ blame ⦂ A
compatible-blame {Γ}{A} γ = 𝓔-blame

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ =
     let ⊢𝓥γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ A ⟧ (γ x)
         ⊢𝓥γx = lookup-𝓖 Γ γ ∋x in
     let ⊢𝓔γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (γ x)
         ⊢𝓔γx = 𝓥⇒𝓔{A}{𝓖⟦ Γ ⟧ γ} ⊢𝓥γx in
     ⊢𝓔γx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} γ =
     let ⊢𝓥n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝓥n = ⊢ᵒ-intro λ { zero x → tt ; (suc k) x → refl} in
     let ⊢𝓔n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝓔n = 𝓥⇒𝓔{$ₜ ′ℕ}{𝓖⟦ Γ ⟧ γ} ⊢𝓥n in
     ⊢𝓔n

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} γ =
     let ⊢𝓥b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝓥b = ⊢ᵒ-intro λ { zero x → tt ; (suc k) x → refl} in
     let ⊢𝓔b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝓔b = 𝓥⇒𝓔{$ₜ ′𝔹}{𝓖⟦ Γ ⟧ γ} ⊢𝓥b in
     ⊢𝓔b

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢𝓔LM
 where
 ⊢𝓔L : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⇒ B ⟧ (⟪ γ ⟫ L)
 ⊢𝓔L = ⊨L γ

 ⊢𝓔M : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)
 ⊢𝓔M = ⊨M γ

 ⊢𝓔LM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))
 ⊢𝓔LM = 𝓔-frame {F = □· (⟪ γ ⟫ M)} ⊢𝓔L
                 (⊢ᵒ-∀-intro λ V → ⊢ᵒ-→-intro (⊢ᵒ-→-intro ⊢𝓔VM))
  where
  𝓟₁ = λ V → 𝓥⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢𝓔VM : ∀{V} → 𝓟₁ V ⊢ᵒ 𝓔⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢𝓔VM {V} = sucP⊢ᵒQ λ 𝓥Vsn →
       let v = 𝓥⇒Value (A ⇒ B) V 𝓥Vsn in
       let 𝓟₁⊢𝓔M : 𝓟₁ V ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)
           𝓟₁⊢𝓔M = ⊢ᵒ-weaken (⊢ᵒ-weaken ⊢𝓔M) in
       𝓔-frame {F = v ·□} 𝓟₁⊢𝓔M
           (⊢ᵒ-∀-intro λ V → ⊢ᵒ-→-intro (⊢ᵒ-→-intro ⊢𝓔VW))
   where
   𝓟₂ = λ V W → 𝓥⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝓥⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ
                 ∷ 𝓖⟦ Γ ⟧ γ
   ⊢𝓔VW : ∀{V W} → 𝓟₂ V W ⊢ᵒ 𝓔⟦ B ⟧ (V · W)
   ⊢𝓔VW {V}{W} =
     let ⊢𝓥V : 𝓟₂ V W ⊢ᵒ 𝓥⟦ A ⇒ B ⟧ V
         ⊢𝓥V = ⊢ᵒ-weaken (⊢ᵒ-weaken ⊢ᵒ-hyp) in
     let ⊢𝓥W : 𝓟₂ V W ⊢ᵒ 𝓥⟦ A ⟧ W
         ⊢𝓥W = ⊢ᵒ-hyp in
     ⊢ᵒ-sucP ⊢𝓥W λ 𝓥Wsn →
     let w = 𝓥⇒Value A W 𝓥Wsn in
     V-fun-elim ⊢𝓥V λ {N′ refl 𝓥W→𝓔NW →
     let prog : 𝓟₂ (ƛ N′) W ⊢ᵒ progress B (ƛ N′ · W)
         prog = (⊢ᵒ-inj₂ (⊢ᵒ-inj₁ (⊢ᵒ-Sᵒ-intro (_ , (β w))))) in
     let pres : 𝓟₂ (ƛ N′) W ⊢ᵒ preservation B (ƛ N′ · W)
         pres = ⊢ᵒ-∀-intro λ N → ⊢ᵒ-→-intro (Sᵒ⊢ᵒ λ {r →
               let ⊢▷𝓔N′W = ⊢ᵒ-→-elim 𝓥W→𝓔NW (⊢ᵒ-mono ⊢𝓥W) in
               let eq = deterministic r (β w) in
                subst (λ N → 𝓟₂ (ƛ N′) W ⊢ᵒ ▷ᵒ 𝓔⟦ B ⟧ N) (sym eq) ⊢▷𝓔N′W}) in
     𝓔-intro prog pres
     }

compatible-lambda : ∀{Γ}{A}{B}{N}
   → (A ∷ Γ) ⊨ N ⦂ B
     -------------------
   → Γ ⊨ (ƛ N) ⦂ (A ⇒ B)
compatible-lambda {Γ}{A}{B}{N} ⊨N γ = ⊢𝓔γλN
 where
 ⊢𝓔γλN : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⇒ B ⟧ (ƛ (⟪ ext γ ⟫ N))
 ⊢𝓔γλN =
   let eq = V-fun{A}{B}{⟪ ext γ ⟫ N} in
   𝓥⇒𝓔 (≡ᵒ⇒⊢ᵒ (⊢ᵒ-∀-intro λ W → ⊢ᵒ-→-intro G) (≡ᵒ-sym eq))
   where
   G : ∀{W} → ▷ᵒ 𝓥⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ 𝓔⟦ B ⟧ (⟪ W • γ ⟫ N)
   G {W} =
     let ⊢𝓥W→𝓔N[W] : 𝓖⟦ Γ ⟧ γ ⊢ᵒ (▷ᵒ (𝓥⟦ A ⟧ W) →ᵒ ▷ᵒ 𝓔⟦ B ⟧ (⟪ W • γ ⟫ N))
         ⊢𝓥W→𝓔N[W] = ⊢ᵒ-▷→{P = 𝓥⟦ A ⟧ W} (⊢ᵒ-mono (⊢ᵒ-→-intro (⊨N (W • γ))))
     in
     let ⊢▷𝓥W : ▷ᵒ 𝓥⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ ▷ᵒ 𝓥⟦ A ⟧ W
         ⊢▷𝓥W = ⊢ᵒ-hyp in
     ⊢ᵒ-→-elim (⊢ᵒ-weaken ⊢𝓥W→𝓔N[W]) ⊢▷𝓥W

compatible-inject : ∀{Γ}{G}{g}{M}
  → Γ ⊨ M ⦂ G
  → Γ ⊨ op-inject{G} g ⦅ cons (ast M) nil ⦆ ⦂ ★
compatible-inject {Γ}{G}{g}{M} ⊨M γ = 𝓔Mg!
 where
 ⊢𝓔M : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ G ⟧ (⟪ γ ⟫ M)
 ⊢𝓔M = ⊨M γ
  
 𝓔Mg! : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ ★ ⟧ ((⟪ γ ⟫ M) ⟨ g !⟩)
 𝓔Mg! = 𝓔-frame {F = □⟨ g !⟩} ⊢𝓔M
            (⊢ᵒ-∀-intro λ V → ⊢ᵒ-→-intro (⊢ᵒ-→-intro ⊢𝓔Vg!))
  where
  𝓟₁ = λ V → 𝓥⟦ G ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢𝓔Vg! : ∀{V} → 𝓟₁ V ⊢ᵒ 𝓔⟦ ★ ⟧ (V ⟨ g !⟩)
  ⊢𝓔Vg!{V} =
   let ⊢𝓥V : 𝓟₁ V ⊢ᵒ 𝓥⟦ G ⟧ V
       ⊢𝓥V = ⊢ᵒ-hyp in
   ⊢ᵒ-sucP ⊢𝓥V λ 𝓥Vsn →
   let v = 𝓥⇒Value G V 𝓥Vsn in
   let eq = V-dyn{G}{V}{g} in
   𝓥⇒𝓔 ((≡ᵒ⇒⊢ᵒ (⊢ᵒ-×-intro (⊢ᵒ-Sᵒ-intro v) (⊢ᵒ-mono ⊢𝓥V)) (≡ᵒ-sym eq)))

red-inj-proj : ∀{G}{H}{g}{h}{W}
   → Value W
   → reducible (op-project{H} h
                  ⦅ cons (ast (op-inject{G} g ⦅ cons (ast W) nil ⦆)) nil ⦆)
red-inj-proj {G} {H} {g} {h} {W} w
    with g ≡ᵍ h
... | yes refl = W , (collapse w g h refl)
... | no neq = blame , (collide w g h neq refl)

compatible-project : ∀{Γ}{H}{h}{M}
  → Γ ⊨ M ⦂ ★
  → Γ ⊨ op-project{H} h ⦅ cons (ast M) nil ⦆ ⦂ H
compatible-project {Γ}{H}{h}{M} ⊨M γ = 𝓔Mh?
 where
 ⊢𝓔M : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ ★ ⟧ (⟪ γ ⟫ M)
 ⊢𝓔M = ⊨M γ
  
 𝓔Mh? : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ H ⟧ ((⟪ γ ⟫ M) ⟨ h ?⟩)
 𝓔Mh? = 𝓔-frame {F = □⟨ h ?⟩} ⊢𝓔M
            (⊢ᵒ-∀-intro λ V → ⊢ᵒ-→-intro (⊢ᵒ-→-intro ⊢𝓔Vh?))
  where
  𝓟₁ = λ V → 𝓥⟦ ★ ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢𝓔Vh? : ∀{V} → 𝓟₁ V ⊢ᵒ 𝓔⟦ H ⟧ (V ⟨ h ?⟩)
  ⊢𝓔Vh?{V} =
   let ⊢𝓥V : 𝓟₁ V ⊢ᵒ 𝓥⟦ ★ ⟧ V
       ⊢𝓥V = ⊢ᵒ-hyp in
   V-dyn-elim ⊢𝓥V λ { W G g refl ⊢w×▷𝓥W→𝓔Vh! →
   let ⊢w = ⊢ᵒ-proj₁ ⊢w×▷𝓥W→𝓔Vh! in
   ⊢ᵒ-sucP ⊢w λ{n} w →
   let prog : 𝓟₁ (W ⟨ g !⟩) ⊢ᵒ progress H ((W ⟨ g !⟩) ⟨ h ?⟩)
       prog = ⊢ᵒ-inj₂ (⊢ᵒ-inj₁ (⊢ᵒ-Sᵒ-intro (red-inj-proj w))) in

   𝓔-intro prog {!!}
   }
