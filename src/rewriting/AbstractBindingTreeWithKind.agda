{-# OPTIONS --rewriting #-}

{-
  -------------------------------- !!! !!! --------------------------------
  This module extends rewriting.AbstractBindingTree with variable kinding
  -------------------------------- +++ +++ --------------------------------
-}
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; suc-injective)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no; contradiction)
open import ScopedTuple
open import Sig
open import Var
open import Function using (case_of_)
open import Structures using (extensionality)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module rewriting.AbstractBindingTreeWithKind {ℓ}
  -- Parameters of the module
  (Op : Set ℓ)
  (sig : Op → List Sig)
  where

+k=k : ∀ {k : ℕ} → Relation.Nullary.map′
                   (Data.Nat.Properties.≡ᵇ⇒≡ k k) (Data.Nat.Properties.≡⇒≡ᵇ k k)
                   (Data.Bool.T? (k Data.Nat.≡ᵇ k)) ≡ yes refl
+k=k {k} with k ≟ k
... | yes refl = refl
... | no k≠k = contradiction refl k≠k
{-# REWRITE +k=k #-}

data Args : List Sig → Set ℓ

data ABT : Set ℓ where
  `_of_ : Var → ℕ → ABT
  _⦅_⦆ : (op : Op) → Args (sig op) → ABT

data Arg : Sig → Set ℓ where
  ast : ABT → Arg ■
  bind : ∀{b} → ℕ → Arg b → Arg (ν b)

data Args where
  nil : Args []
  cons : ∀{b bs} → Arg b → Args bs → Args (b ∷ bs)

{----------------------------------------------------------------------------
 Renaming
----------------------------------------------------------------------------}

Rename : Set
Rename = Var → Var

infixr 6 _•ᵣ_
_•ᵣ_ : Var → Rename → Rename
(y •ᵣ ρ) 0 = y
(y •ᵣ ρ) (suc x) = ρ x

⟰ᵣ : Rename → Rename
⟰ᵣ ρ x = suc (ρ x)

extr : Rename → Rename
extr ρ = 0 •ᵣ ⟰ᵣ ρ

rename : Rename → ℕ → ABT → ABT
rename-arg : Rename → ℕ → {b : Sig} → Arg b → Arg b
rename-args : Rename → ℕ → {bs : List Sig} → Args bs → Args bs

rename ρ 𝑘 (` x of 𝑗) with 𝑘 ≟ 𝑗
... | yes refl = ` (ρ x) of 𝑗    -- we only rename the correct kind of variables
... | no _     = ` x of 𝑗
rename ρ 𝑘 (op ⦅ args ⦆) = op ⦅ rename-args ρ 𝑘 args ⦆
rename-arg ρ 𝑘 (ast M) = ast (rename ρ 𝑘 M)
rename-arg ρ 𝑘 (bind 𝑗 M) with 𝑘 ≟ 𝑗
... | yes refl = bind 𝑗 (rename-arg (extr ρ) 𝑘 M)
... | no _     = bind 𝑗 (rename-arg ρ 𝑘 M)
rename-args ρ 𝑘 nil = nil
rename-args ρ 𝑘 (cons arg args) = cons (rename-arg ρ 𝑘 arg) (rename-args ρ 𝑘 args)

{----------------------------------------------------------------------------
 Substitution
----------------------------------------------------------------------------}

Subst : Set ℓ
Subst = Var → ABT

infixr 6 _•_
_•_ : ABT → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

{----------------------------------------------------------------------------
 The following module is for internal use only.
 ----------------------------------------------------------------------------}
module Private where

  ⟰ : Subst → ℕ → Subst
  ⟰ σ 𝑘 x = rename suc 𝑘 (σ x)

  exts : Subst → ℕ → Subst
  exts σ 𝑘 = (` 0 of 𝑘) • (⟰ σ 𝑘)

  sub : Subst → ℕ → ABT → ABT
  sub-arg : Subst → ℕ → {b : Sig} → Arg b → Arg b
  sub-args : Subst → ℕ → {bs : List Sig} → Args bs → Args bs

  sub σ 𝑘 (` x of 𝑗) with 𝑘 ≟ 𝑗
  ... | yes refl = σ x
  ... | no _     = ` x of 𝑗
  sub σ 𝑘 (op ⦅ args ⦆) = op ⦅ sub-args σ 𝑘 args ⦆
  sub-arg σ 𝑘 (ast M) = ast (sub σ 𝑘 M)
  sub-arg σ 𝑘 (bind 𝑗 M) with 𝑘 ≟ 𝑗
  ... | yes refl = bind 𝑗 (sub-arg (exts σ 𝑗) 𝑘 M)
  ... | no _     = bind 𝑗 (sub-arg σ 𝑘 M)
  sub-args σ 𝑘 nil = nil
  sub-args σ 𝑘 (cons arg args) = cons (sub-arg σ 𝑘 arg) (sub-args σ 𝑘 args)

  {- TODO: make ren abstract -}
  ren : Rename → ℕ → Subst
  ren ρ 𝑘 x = ` (ρ x) of 𝑘

  abstract
    infixr 5 _⨟_of_
    _⨟_of_ : Subst → Subst → ℕ → Subst
    (σ ⨟ τ of 𝑘) x = sub τ 𝑘 (σ x)


  abstract
    seq-def : ∀ σ τ 𝑘 x → (σ ⨟ τ of 𝑘) x ≡ sub τ 𝑘 (σ x)
    seq-def σ τ 𝑘 x = refl
  {-# REWRITE seq-def #-}

  cons-seq-dist : ∀ σ τ 𝑘 M → (M • σ) ⨟ τ of 𝑘 ≡ sub τ 𝑘 M • (σ ⨟ τ of 𝑘)
  cons-seq-dist σ τ 𝑘 M = extensionality ♠
      where
      ♠ : ∀ x → ((M • σ) ⨟ τ of 𝑘) x ≡ (sub τ 𝑘 M • (σ ⨟ τ of 𝑘)) x
      ♠ zero = refl
      ♠ (suc x) = refl
  {-# REWRITE cons-seq-dist #-}

  ext-ren : ∀{ρ 𝑘} → (` 0 of 𝑘) • (⟰ (ren ρ 𝑘) 𝑘) ≡ ren (extr ρ) 𝑘
  ext-ren {ρ} {𝑘} = extensionality ♠
      where
      ♠ : ∀ x → exts (ren ρ 𝑘) 𝑘 x ≡ ren (extr ρ) 𝑘 x
      ♠ zero = refl
      ♠ (suc x) = refl
  {-# REWRITE ext-ren #-}

  rename-ren : ∀{ρ 𝑘 M} → rename ρ 𝑘 M ≡ sub (ren ρ 𝑘) 𝑘 M
  rename-ren-arg : ∀{ρ 𝑘 b}{arg : Arg b} → rename-arg ρ 𝑘 arg ≡ sub-arg (ren ρ 𝑘) 𝑘 arg
  rename-ren-args : ∀{ρ 𝑘 bs}{args : Args bs}
     → rename-args ρ 𝑘 args ≡ sub-args (ren ρ 𝑘) 𝑘 args
  rename-ren {ρ} {𝑘} {` x of 𝑗} with 𝑘 ≟ 𝑗
  ... | yes refl = refl
  ... | no neq = refl
  rename-ren {ρ} {𝑘} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) rename-ren-args
  rename-ren-arg {ρ} {𝑘} {.■} {ast M} = cong ast (rename-ren {ρ} {𝑘} {M})
  rename-ren-arg {ρ} {𝑘} {.(ν _)} {bind 𝑗 arg} with 𝑘 ≟ 𝑗
  ... | yes refl = cong (bind 𝑘) (rename-ren-arg {_} {𝑘} {_} {arg})
  ... | no neq = cong (bind 𝑗) (rename-ren-arg {ρ} {𝑘} {_} {arg})
  rename-ren-args {ρ} {𝑘} {.[]} {nil} = refl
  rename-ren-args {ρ} {𝑘} {.(_ ∷ _)} {cons arg args} =
      cong₂ cons (rename-ren-arg {ρ} {𝑘} {_} {arg}) rename-ren-args
  {-# REWRITE rename-ren #-}

  ext-ren-sub : ∀ {ρ}{τ}{𝑘} → exts (ren ρ 𝑘) 𝑘 ⨟ exts τ 𝑘 of 𝑘 ≡ exts (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘
  ext-ren-sub {ρ}{τ}{𝑘} = extensionality ♠
    where
    ♠ : ∀ x → (exts (ren ρ 𝑘) 𝑘 ⨟ (exts τ 𝑘) of 𝑘) x ≡ (exts (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘) x
    ♠ zero = refl
    ♠ (suc x) = refl
  {-# REWRITE ext-ren-sub #-}

  private
    ext-ren-η : ∀ {ρ 𝑘} → ((` 0 of 𝑘) • (λ x → ` suc (ρ x) of 𝑘)) ≡ ren (extr ρ) 𝑘
    ext-ren-η {ρ}{𝑘} = extensionality ♠
      where
      ♠ : ∀ x → ((` 0 of 𝑘) • (λ y → ` suc (ρ y) of 𝑘)) x ≡ ren (extr ρ) 𝑘 x
      ♠ zero = refl
      ♠ (suc x) = refl

  ren-sub : ∀ {τ ρ 𝑘 M} → sub τ 𝑘 (sub (ren ρ 𝑘) 𝑘 M) ≡ sub (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘 M
  ren-sub-arg : ∀ {τ ρ 𝑘 b}{arg : Arg b}
     → sub-arg τ 𝑘 (sub-arg (ren ρ 𝑘) 𝑘 arg) ≡ sub-arg (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘 arg
  ren-sub-args : ∀ {τ ρ 𝑘 bs}{args : Args bs}
     → sub-args τ 𝑘 (sub-args (ren ρ 𝑘) 𝑘 args) ≡ sub-args (ren ρ 𝑘 ⨟ τ of 𝑘) 𝑘 args
  ren-sub {τ} {ρ} {𝑘} {` x of 𝑗} with 𝑘 ≟ 𝑗
  ... | yes refl = refl
  ... | no k≠j with 𝑘 ≟ 𝑗
  ... | yes k=j = contradiction k=j k≠j
  ... | no _ = refl
  ren-sub {τ} {ρ} {𝑘} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) ren-sub-args
  ren-sub-arg {τ} {ρ} {𝑘} {.■} {ast M} = cong ast (ren-sub{τ}{ρ}{𝑘}{M})
  ren-sub-arg {τ} {ρ} {𝑘} {.(ν _)} {bind 𝑗 arg} with 𝑘 ≟ 𝑗
  ... | yes refl = cong (bind 𝑘) (ren-sub-arg {exts τ 𝑘} {extr ρ} {𝑘} {arg = arg})
  ... | no k≠j with 𝑘 ≟ 𝑗
  ...   | yes k=j = contradiction k=j k≠j
  ...   | no k≠j  = cong (bind 𝑗) (ren-sub-arg {τ} {ρ} {𝑘} {arg = arg})
  ren-sub-args {τ} {ρ} {𝑘} {.[]} {nil} = refl
  ren-sub-args {τ} {ρ} {𝑘} {.(_ ∷ _)} {cons arg args} =
     cong₂ cons (ren-sub-arg {arg = arg}) ren-sub-args
  {-# REWRITE ren-sub #-}


  sub-ren : ∀ {ρ σ 𝑘 M} → sub (ren ρ 𝑘) 𝑘 (sub σ 𝑘 M) ≡ sub (σ ⨟ ren ρ 𝑘 of 𝑘) 𝑘 M
  sub-ren-arg : ∀ {ρ σ 𝑘 b} {arg : Arg b} → sub-arg (ren ρ 𝑘) 𝑘 (sub-arg σ 𝑘 arg) ≡ sub-arg (σ ⨟ ren ρ 𝑘 of 𝑘) 𝑘 arg
  sub-ren-args : ∀ {ρ σ 𝑘 bs} {args : Args bs} → sub-args (ren ρ 𝑘) 𝑘 (sub-args σ 𝑘 args) ≡ sub-args (σ ⨟ ren ρ 𝑘 of 𝑘) 𝑘 args
  sub-ren {ρ} {σ} {𝑘} {` x of 𝑗} with 𝑘 ≟ 𝑗
  ... | yes refl = refl
  ... | no k≠j with 𝑘 ≟ 𝑗
  ... | yes k=j = contradiction k=j k≠j
  ... | no _ = refl
  sub-ren {ρ} {σ} {𝑘} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-ren-args
  sub-ren-arg {ρ} {σ} {𝑘} {.■} {ast M} = cong ast (sub-ren{ρ}{σ}{𝑘}{M})
  sub-ren-arg {ρ} {σ} {𝑘} {.(ν _)} {bind 𝑗 arg} with 𝑘 ≟ 𝑗
  ... | yes refl = cong (bind 𝑘) (sub-ren-arg {extr ρ} {exts σ 𝑘} {𝑘} {arg = arg})
  ... | no k≠j with 𝑘 ≟ 𝑗
  ...   | yes k=j = contradiction k=j k≠j
  ...   | no k≠j  = cong (bind 𝑗) (sub-ren-arg {ρ} {σ} {𝑘} {arg = arg})
  sub-ren-args {ρ} {σ} {𝑘} {.[]} {nil} = refl
  sub-ren-args {ρ} {σ} {𝑘} {.(_ ∷ _)} {cons arg args} =
    cong₂ cons (sub-ren-arg {arg = arg}) sub-ren-args
  {-# REWRITE sub-ren #-}

  sub-sub : ∀{σ τ 𝑘 M} → sub τ 𝑘 (sub σ 𝑘 M) ≡ sub (σ ⨟ τ of 𝑘) 𝑘 M
  sub-sub-arg : ∀{σ τ 𝑘 b}{arg : Arg b} → sub-arg τ 𝑘 (sub-arg σ 𝑘 arg) ≡ sub-arg (σ ⨟ τ of 𝑘) 𝑘 arg
  sub-sub-args : ∀{σ τ 𝑘 bs}{args : Args bs} → sub-args τ 𝑘 (sub-args σ 𝑘 args) ≡ sub-args (σ ⨟ τ of 𝑘) 𝑘 args
  sub-sub {σ} {τ} {𝑘} {` x of 𝑗} with 𝑘 ≟ 𝑗
  ... | yes refl = refl
  ... | no k≠j with 𝑘 ≟ 𝑗
  ... | yes k=j = contradiction k=j k≠j
  ... | no _ = refl
  sub-sub {σ} {τ} {𝑘} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-sub-args
  sub-sub-arg {σ} {τ} {𝑘} {.■} {ast M} = cong ast (sub-sub{σ}{τ}{𝑘}{M})
  sub-sub-arg {σ} {τ} {𝑘} {.(ν _)} {bind 𝑗 arg} with 𝑘 ≟ 𝑗
  ... | yes refl = cong (bind 𝑘) (sub-sub-arg {exts σ 𝑘} {exts τ 𝑘} {𝑘} {arg = arg})
  ... | no k≠j with 𝑘 ≟ 𝑗
  ...   | yes k=j = contradiction k=j k≠j
  ...   | no k≠j  = cong (bind 𝑗) (sub-sub-arg {σ} {τ} {𝑘} {arg = arg})
  sub-sub-args {σ} {τ} {𝑘} {.[]} {nil} = refl
  sub-sub-args {σ} {τ} {𝑘} {.(_ ∷ _)} {cons arg args} = cong₂ cons (sub-sub-arg {arg = arg}) sub-sub-args
  {-# REWRITE sub-sub #-}

  shift-seq : ∀{σ 𝑘} → ⟰ σ 𝑘 ≡ (σ ⨟ ren suc 𝑘 of 𝑘)
  shift-seq {σ} = refl

  idᵣ : Rename
  idᵣ x = x

  extr-id : (0 •ᵣ ⟰ᵣ idᵣ) ≡ idᵣ {- extr idᵣ ≡ idᵣ -}
  extr-id = extensionality aux
    where
    aux : ∀ x → extr idᵣ x ≡ idᵣ x
    aux zero = refl
    aux (suc x) = refl
  {-# REWRITE extr-id #-}

  id : ℕ → Subst
  id 𝑘 x = ` x of 𝑘

  ext-id : ∀ {𝑘} → exts (id 𝑘) 𝑘 ≡ id 𝑘
  ext-id = refl


  sub-id : ∀ {M 𝑘} → sub (id 𝑘) 𝑘 M ≡ M
  sub-arg-id : ∀ {𝑘 b}{arg : Arg b} → sub-arg (id 𝑘) 𝑘 arg ≡ arg
  sub-args-id : ∀ {𝑘 bs}{args : Args bs} → sub-args (id 𝑘) 𝑘 args ≡ args
  sub-id {` x of 𝑗} {𝑘} with 𝑘 ≟ 𝑗
  ... | yes refl = refl
  ... | no k≠j with 𝑘 ≟ 𝑗
  ... | yes k=j = contradiction k=j k≠j
  ... | no _ = refl
  sub-id {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-args-id
  sub-arg-id {𝑘} {.■} {ast M} = cong ast sub-id
  sub-arg-id {𝑘} {.(ν _)} {bind 𝑗 arg} with 𝑘 ≟ 𝑗
  ... | yes refl = cong (bind 𝑘) (sub-arg-id {𝑘} {arg = arg})
  ... | no k≠j with 𝑘 ≟ 𝑗
  ...   | yes k=j = contradiction k=j k≠j
  ...   | no k≠j  = cong (bind 𝑗) (sub-arg-id {𝑘} {arg = arg})
  sub-args-id {𝑘} {.[]} {nil} = refl
  sub-args-id {𝑘} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-arg-id sub-args-id
  {-# REWRITE sub-id #-}

{----------------------------------------------------------------------------
 Public
----------------------------------------------------------------------------}

abstract {- experimenting with making ren abstract -Jeremy -}
  ren : Rename → ℕ → Subst
  ren ρ 𝑘 = Private.ren ρ 𝑘

  ren-def : ∀ ρ 𝑘 x → ren ρ 𝑘 x ≡ ` ρ x of 𝑘
  ren-def ρ 𝑘 x = refl

↑ : ℕ → Subst
↑ 𝑘 = ren suc 𝑘

up-def : ↑ ≡ ren suc
up-def = refl

abstract
  infixr 5 _⨟_of_
  _⨟_of_ : Subst → Subst → ℕ → Subst
  σ ⨟ τ of 𝑘 = Private._⨟_of_ σ τ 𝑘

  id : ℕ → Subst
  id 𝑘 = Private.id 𝑘

ext : Subst → ℕ → Subst
ext σ 𝑘 = (` 0 of 𝑘) • (σ ⨟ ↑ 𝑘 of 𝑘)

abstract
  -- Phil: you're using semicolon, so this should be postfix
  ⟪_⟫ : Subst → ℕ → ABT → ABT
  ⟪ σ ⟫ 𝑘 M = Private.sub σ 𝑘 M

  -- Phil: try switching + to *
  ⟪_⟫₊ : Subst → ℕ → {bs : List Sig} → Args bs → Args bs
  ⟪ σ ⟫₊ 𝑘 args = Private.sub-args σ 𝑘 args

  ⟪_⟫ₐ : Subst → ℕ → {b : Sig} → Arg b → Arg b
  ⟪ σ ⟫ₐ 𝑘 arg = Private.sub-arg σ 𝑘 arg

  id-var : ∀{x 𝑘} → (id 𝑘 x) ≡ (` x of 𝑘)
  id-var = refl
  {-# REWRITE id-var #-}

  sub-var : ∀ σ 𝑘 x → ⟪ σ ⟫ 𝑘 (` x of 𝑘) ≡ σ x
  sub-var σ 𝑘 x = refl
  {-# REWRITE sub-var #-}

  sub-op : ∀{σ : Subst}{op : Op}{args : Args (sig op)} {𝑘}
     → ⟪ σ ⟫ 𝑘 (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ 𝑘 args ⦆
  sub-op = refl
  {-# REWRITE sub-op #-}

  sub-arg-ast : ∀{σ M}{𝑘} → ⟪ σ ⟫ₐ 𝑘 (ast M) ≡ ast (⟪ σ ⟫ 𝑘 M)
  sub-arg-ast = refl
  {-# REWRITE sub-arg-ast #-}

  sub-arg-bind : ∀{σ b}{arg : Arg b}{𝑘}
     → ⟪ σ ⟫ₐ 𝑘 (bind 𝑘 arg) ≡ bind 𝑘 (⟪ ext σ 𝑘 ⟫ₐ 𝑘 arg)
  sub-arg-bind = refl
  {-# REWRITE sub-arg-bind #-}

  sub-args-nil : ∀{σ}{𝑘} → ⟪ σ ⟫₊ 𝑘 nil ≡ nil
  sub-args-nil = refl
  {-# REWRITE sub-args-nil #-}

  sub-args-cons : ∀{σ}{b}{bs}{arg : Arg b}{args : Args bs} {𝑘}
     → ⟪ σ ⟫₊ 𝑘 (cons arg args) ≡ cons (⟪ σ ⟫ₐ 𝑘 arg) (⟪ σ ⟫₊ 𝑘 args)
  sub-args-cons = refl
  {-# REWRITE sub-args-cons #-}

  sub-tail : ∀ σ 𝑘 M → (↑ 𝑘) ⨟ M • σ of 𝑘 ≡ σ
  sub-tail σ 𝑘 M = extensionality ♠
      where
      ♠ : ∀ x → ((↑ 𝑘) ⨟ M • σ of 𝑘) x ≡ σ x
      ♠ zero = refl
      ♠ (suc x) = refl
  {-# REWRITE sub-tail #-}

  sub-id : ∀ M 𝑘 → ⟪ id 𝑘 ⟫ 𝑘 M ≡ M
  sub-id M 𝑘 = Private.sub-id {M} {𝑘}
  {-# REWRITE sub-id #-}

  sub-eta : ∀ σ 𝑘 → (⟪ σ ⟫ 𝑘 (` 0 of 𝑘)) • ((↑ 𝑘) ⨟ σ of 𝑘) ≡ σ
  sub-eta σ 𝑘 = extensionality ♥
    where
    ♥ : ∀ x → ((⟪ σ ⟫ 𝑘 (` 0 of 𝑘)) • ((↑ 𝑘) ⨟ σ of 𝑘)) x ≡ σ x
    ♥ zero = refl
    ♥ (suc x) = refl
  {-# REWRITE sub-eta #-}

  sub-id-right : ∀ σ 𝑘 → σ ⨟ (id 𝑘) of 𝑘 ≡ σ
  sub-id-right σ 𝑘 = refl
  {-# REWRITE sub-id-right #-}

  sub-id-left : ∀ σ 𝑘 → (id 𝑘) ⨟ σ of 𝑘 ≡ σ
  sub-id-left σ 𝑘 = refl
  {-# REWRITE sub-id-left #-}

  sub-assoc : ∀ σ τ θ 𝑘 → (σ ⨟ τ of 𝑘) ⨟ θ of 𝑘 ≡ σ ⨟ (τ ⨟ θ of 𝑘) of 𝑘
  sub-assoc σ τ θ 𝑘 = refl
  {-# REWRITE sub-assoc #-}

  cons-seq : ∀ σ τ M 𝑘 → (M • σ) ⨟ τ of 𝑘 ≡ (⟪ τ ⟫ 𝑘 M) • (σ ⨟ τ of 𝑘)
  cons-seq σ τ M 𝑘 = refl
  {-# REWRITE cons-seq #-}

  compose-sub : ∀ σ τ M 𝑘 → ⟪ τ ⟫ 𝑘 (⟪ σ ⟫ 𝑘 M) ≡ ⟪ σ ⨟ τ of 𝑘 ⟫ 𝑘 M
  compose-sub σ τ M 𝑘 = refl
  {-# REWRITE compose-sub #-}

  cons-zero-up : ∀ 𝑘 → (` 0 of 𝑘) • (↑ 𝑘) ≡ id 𝑘
  cons-zero-up 𝑘 = refl
  {-# REWRITE cons-zero-up #-}

  seq-def : ∀ σ τ 𝑘 x → (σ ⨟ τ of 𝑘) x ≡ ⟪ τ ⟫ 𝑘 (σ x)
  seq-def σ τ 𝑘 x = refl

  up-var : ∀ 𝑘 x → (↑ 𝑘) x ≡ ` suc x of 𝑘
  up-var 𝑘 x = refl

  ren-extr-def : ∀ ρ 𝑘 → ren (extr ρ) 𝑘 ≡ (` 0 of 𝑘) • (ren ρ 𝑘 ⨟ ↑ 𝑘 of 𝑘)
  ren-extr-def ρ 𝑘 = refl
  {-# REWRITE ren-extr-def #-}

_[_]of_ : ABT → ABT → ℕ → ABT
N [ M ]of 𝑘 =  ⟪ M • id 𝑘 ⟫ 𝑘 N

_〔_〕of_ : ABT → ABT → ℕ → ABT
N 〔 M 〕of 𝑘 = ⟪ ext (M • id 𝑘) 𝑘 ⟫ 𝑘 N

substitution : ∀{M N L} {𝑘} → (M [ N ]of 𝑘) [ L ]of 𝑘 ≡ (M 〔 L 〕of 𝑘) [ N [ L ]of 𝑘 ]of 𝑘
substitution = refl

exts-sub-cons : ∀ {σ 𝑘 N V} → (⟪ ext σ 𝑘 ⟫ 𝑘 N) [ V ]of 𝑘 ≡ ⟪ V • σ ⟫ 𝑘 N
exts-sub-cons = refl
