{-# OPTIONS --cubical --safe --guardedness -WnoUnsupportedIndexedMatch #-}

module Talks.Cubes where

------------------------------------------------------------------------------
--
--                         Programming with Cubes
--
--          Vikraman Choudhury    <vikraman.choudhury@strath.ac.uk>
--               Rin Liu          <rin.liu@strath.ac.uk>
--
--               Mathematically Structured Programming group
--                   Computer and Information Sciences
--                       University of Strathclyde
--
------------------------------------------------------------------------------

















------------------------------------------------------------------------------
-- We'll be using the Cubical Agda standard Library:

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; subst to tpt
           )
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
import Cubical.Functions.Logic as L
import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Maybe hiding (rec)
open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to ⋆)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)

variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ

------------------------------------------------------------------------------






------------------------------------------------------------------------------
-- Homotopy Type Theory
------------------------------------------------------------------------------

-- funExt : {B : A → I → Type ℓ'}
--   {f : (x : A) → B x i0} {g : (x : A) → B x i1}
--   → ((x : A) → PathP (B x) (f x) (g x))
--   → PathP (λ i → (x : A) → B x i) f g
-- funExt p i x = p x i

-- ua


















------------------------------------------------------------------------------
-- Points, Lines, Squares, Cubes...
------------------------------------------------------------------------------

-- TODO








------------------------------------------------------------------------------
-- Lists, Vectors
------------------------------------------------------------------------------

module Lists where

  data List {ℓ} (A : Type ℓ) : Type ℓ where
    []  : List A
    _∷_ : A → List A → List A

  head : {A : Type ℓ} → List A → Maybe A
  head [] = nothing
  head (x ∷ xs) = just x

module Vectors where

  data Vec {ℓ} (A : Type ℓ) : ℕ → Type ℓ where
    []  : Vec A zero
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

  head : {A : Type ℓ} {n : ℕ} → Vec A (suc n) → A
  head (x ∷ xs) = x

------------------------------------------------------------------------------










------------------------------------------------------------------------------
-- HITs
------------------------------------------------------------------------------

module Circle where

  data S¹ : Type where
    base : S¹
    loop : base ≡ base

  ΩS¹ = base ≡ base

  module S¹Elim where

    module _ (P : S¹ → Type ℓ')
      (base* : P base)
      (loop* : PathP (λ i → P (loop i)) base* base*) where

      ind : (x : S¹) → P x
      ind base = base*
      ind (loop i) = loop* i

    module _ (P : Type ℓ')
      (base* : P)
      (loop* : base* ≡ base*) where

      rec : (x : S¹) → P
      rec = ind (λ _ → P) base* loop*

  data ℤ : Type where
    pos : ℕ → ℤ
    neg : ℕ → ℤ
    zero : pos 0 ≡ neg 0

  succ : ℤ → ℤ
  succ (pos n) = pos (suc n)
  succ (neg 0) = pos 1
  succ (neg (suc n)) = neg n
  succ (zero i) = pos 1

  pred : ℤ → ℤ
  pred (pos 0) = neg 1
  pred (pos (suc n)) = pos n
  pred (neg n) = neg (suc n)
  pred (zero i) = neg 1

  -- pred zero = neg 0
  -- pred (pos 0) = zero
  -- pred (pos (suc n)) = pos n
  -- pred (neg n) = neg (suc n)

  predSucc : (n : ℤ) → pred (succ n) ≡ n
  predSucc (pos n) = refl
  predSucc (neg 0) = zero
  predSucc (neg (suc x)) = refl
  predSucc (zero i) j = zero (i ∧ j)

  succPred : (n : ℤ) → succ (pred n) ≡ n
  succPred (pos 0) = sym zero
  succPred (pos (suc n)) = refl
  succPred (neg n) = refl
  succPred (zero i) j = zero (i ∨ ~ j)

  succEquiv : ℤ ≃ ℤ
  succEquiv = isoToEquiv (iso succ pred succPred predSucc)

  cover : ℤ → (base ≡ base)
  cover (pos zero) = refl
  cover (pos (suc x)) = loop ∙ cover (pos x)
  cover (neg zero) = refl
  cover (neg (suc x)) = loop ⁻¹ ∙ cover (neg x)
  cover (zero i) = refl

  code : S¹ → Type
  code base = ℤ
  code (loop i) = ua succEquiv i

  encode : (x : S¹) → (base ≡ x) → code x
  encode x p = tpt code p (pos 0)

  encodeDecode : (x : S¹) → (p : base ≡ x) → {!!}
  encodeDecode = {!!}

  decodeEncode : (n : ℤ) → encode base (cover n) ≡ n
  decodeEncode (pos 0) = refl
  decodeEncode (pos (suc n)) = {!!}
  decodeEncode (neg 0) = {!!}
  decodeEncode (neg (suc n)) = {!!}
  decodeEncode (zero i) = {!!}

  pi1 : ΩS¹ ≃ ℤ
  pi1 = isoToEquiv (iso (encode base) cover decodeEncode {!encodeDecode!})















------------------------------------------------------------------------------
-- Spicy Lists, Spicy Vectors
------------------------------------------------------------------------------

module SLists where

  infixr 10 _∷_

  data SList {ℓ} (A : Type ℓ) : Type ℓ where
    []  : SList A
    _∷_ : A → SList A → SList A
    swap : (x y : A) (xs : SList A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
    trunc : isSet (SList A)

  module SListElim where
    module _ (P : SList A → Type ℓ')
         ([]* : P [])
         (_∷*_ : (x : A) {xs : SList A} → P xs → P (x ∷ xs))
         (swap* : (x y : A) {xs : SList A} (p : P xs) → PathP (λ i → P (swap x y xs i)) (x ∷* (y ∷* p)) (y ∷* (x ∷* p)))
         (trunc* : (xs : SList A) → isSet (P xs)) where

      ind : (xs : SList A) → P xs
      ind [] = []*
      ind (x ∷ xs) = x ∷* ind xs
      ind (swap x y xs i) = swap* x y (ind xs) i
      ind (trunc x y p q i j) =
             isSet→SquareP (λ i j → trunc* (trunc x y p q i j)) (apd ind p) (apd ind q) refl refl i j

    module _ {A : Type ℓ} (P : SList A → Type ℓ')
         ([]* : P [])
         (_∷*_ : (x : A) {xs : SList A} → P xs → P (x ∷ xs))
         (trunc* : (xs : SList A) → isProp (P xs)) where

      private
        swap* : (x y : A) {xs : SList A} (p : P xs) → PathP (λ i → P (swap x y xs i)) (x ∷* (y ∷* p)) (y ∷* (x ∷* p))
        swap* x y {xs} p = isProp→PathP (λ i → trunc* (swap x y xs i)) (x ∷* (y ∷* p)) (y ∷* (x ∷* p))

      indProp : (xs : SList A) → P xs
      indProp = ind P []* _∷*_ swap* (λ xs → isProp→isSet (trunc* xs))

    module _ {A : Type ℓ} (P : Type ℓ')
         ([]* : P)
         (_∷*_ : A → P → P)
         (swap* : (x y : A) → (p : P) → Path P (x ∷* (y ∷* p)) (y ∷* (x ∷* p)))
         (trunc* : isSet P) where

      rec : SList A → P
      rec = ind (λ _ → P) []* (λ x {xs} → x ∷*_) (λ x y {xs} → swap* x y) (λ _ → trunc*)

  as : SList ℕ
  as = 1 ∷ 2 ∷ 3 ∷ []

  bs : SList ℕ
  bs = 3 ∷ 2 ∷ 1 ∷ []

  p : as ≡ bs
  p = swap 1 2 _ ∙ ap (2 ∷_) (swap 1 3 _) ∙ swap 2 3 _

  q : as ≡ bs
  q = ap (1 ∷_) (swap 2 3 _) ∙ swap 1 3 _ ∙ ap (3 ∷_) (swap 1 2 _)

  _ : p ≡ q
  _ = trunc as bs p q

  -- head : ∀ {a} {A : Type a} → SList A → Maybe A
  -- head [] = nothing
  -- head (x ∷ xs) = just x
  -- head (swap x y i) = {!!}

module WildMonoid where

  open import Cubical.Data.List

  pattern [_⸴_]       a b         = a ∷ b ∷ []
  pattern [_⸴_⸴_]     a b c       = a ∷ b ∷ c ∷ []
  pattern [_⸴_⸴_⸴_]   a b c d     = a ∷ b ∷ c ∷ d ∷ []
  pattern [_⸴_⸴_⸴_⸴_] a b c d e   = a ∷ b ∷ c ∷ d ∷ e ∷ []

  record WMon {a} (A : Type a) : Type a where
    infixr 10 _⊕_
    field
      e : A
      _⊕_ : A → A → A
      unitl : ∀ x → e ⊕ x ≡ x
      unitr : ∀ x → x ⊕ e ≡ x
      assocr : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  open WMon

  record WMonHom {a b} {A : Type a} {B : Type b} (M : WMon A) (N : WMon B) : Type (ℓ-max a b) where
    private
      module M = WMon M
      module N = WMon N
    field
      ϕ : A → B
      preserves-e : ϕ M.e ≡ N.e
      preserves-⊕ : ∀ x y → ϕ (x M.⊕ y) ≡ ϕ x N.⊕ ϕ y
  open WMonHom

  ListWMon : ∀ {a} {A : Type a} → WMon (List A)
  ListWMon .e = []
  ListWMon ._⊕_ = _++_
  ListWMon .unitl xs = refl
  ListWMon .unitr = ++-unit-r
  ListWMon .assocr = ++-assoc

  η : ∀ {a} {A : Type a} → A → List A
  η a = [ a ]

  module _ {a m} {A : Type a} {M : Type m} (M* : WMon M) where
    private
      module M = WMon M*
      sharp : (A → M) → List A → M
      sharp f [] = M.e
      sharp f (x ∷ xs) = f x M.⊕ sharp f xs

    [_]_♯ = sharp

    module _ (h* : WMonHom ListWMon M*) (f : A → M) where
      private
        module h = WMonHom h*
        sharp-uniq : h.ϕ ∘ η ≡ f → ∀ xs → h.ϕ xs ≡ sharp f xs
        sharp-uniq p [] =
          h.preserves-e
        sharp-uniq p (x ∷ xs) =
            h.preserves-⊕ [ x ] xs
          ∙ ap (M._⊕ h.ϕ xs) (funExt⁻ p x)
          ∙ ap (f x M.⊕_) (sharp-uniq p xs)

      [_]_♯-uniq = sharp-uniq

  𝟙+⟨_⟩-WMon : ∀ {a} (A : Type a) → WMon (𝟙 ⊎ A)
  𝟙+⟨ A ⟩-WMon .e = inl ⋆
  𝟙+⟨ A ⟩-WMon ._⊕_ (inl ⋆) y = y
  𝟙+⟨ A ⟩-WMon ._⊕_ (inr x) y = inr x
  𝟙+⟨ A ⟩-WMon .unitl x = refl
  𝟙+⟨ A ⟩-WMon .unitr (inl ⋆) = refl
  𝟙+⟨ A ⟩-WMon .unitr (inr x) = refl
  𝟙+⟨ A ⟩-WMon .assocr (inl ⋆) y z = refl
  𝟙+⟨ A ⟩-WMon .assocr (inr x) (inl ⋆) z = refl
  𝟙+⟨ A ⟩-WMon .assocr (inr x) (inr y) z = refl

  head : ∀ {a} {A : Type a} → List A → 𝟙 ⊎ A
  head {A = A} = [ 𝟙+⟨ A ⟩-WMon ] inr ♯

  _ : ∀ {a} {A : Type a} → head {A = A} [] ≡ inl ⋆
  _ = refl

  _ : head [ 2 ⸴ 1 ⸴ 3 ] ≡ inr 2
  _ = refl

module CMonoid where

  open SLists

  pattern [_]         a           = a ∷ []
  pattern [_⸴_]       a b         = a ∷ b ∷ []
  pattern [_⸴_⸴_]     a b c       = a ∷ b ∷ c ∷ []
  pattern [_⸴_⸴_⸴_]   a b c d     = a ∷ b ∷ c ∷ d ∷ []
  pattern [_⸴_⸴_⸴_⸴_] a b c d e   = a ∷ b ∷ c ∷ d ∷ e ∷ []

  module _ {ℓ} {A : Type ℓ} where

    infixr 5 _++_

    _++_ : SList A → SList A → SList A
    _++_ = SListElim.rec (SList A → SList A)
      (λ ys → ys)
      (λ x h ys → x ∷ h ys)
      (λ x y h i → λ ys → swap x y (h ys) i)
      (isSet→ trunc)

    ++-unit-r : (xs : SList A) → xs ++ [] ≡ xs
    ++-unit-r = SListElim.indProp (λ xs → xs ++ [] ≡ xs)
      refl
      (λ x {xs} h i → x ∷ h i)
      (λ xs → trunc (xs ++ []) xs)

    ++-assoc : (xs ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
    ++-assoc = SListElim.indProp (λ xs → (ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs)
      (λ ys zs → refl)
      (λ x {xs} h ys zs i → x ∷ h ys zs i)
      (λ xs → isPropΠ2 λ x y → trunc ((xs ++ x) ++ y) (xs ++ x ++ y))

    ∷-comm : (x : A) (xs : SList A) → x ∷ xs ≡ xs ++ [ x ]
    ∷-comm x = SListElim.indProp (λ xs → x ∷ xs ≡ xs ++ [ x ])
      refl
      (λ y {xs} h → swap x y xs ∙ ap (y ∷_) h)
      (λ xs → trunc (x ∷ xs) (xs ++ [ x ]))

    ++-comm : (xs ys : SList A) → xs ++ ys ≡ ys ++ xs
    ++-comm = SListElim.indProp (λ xs → (ys : SList A) → xs ++ ys ≡ ys ++ xs)
      (λ ys → sym (++-unit-r ys))
      (λ x {xs} h ys → ap (x ∷_) (h ys) ∙∙ ap (_++ xs) (∷-comm x ys) ∙∙ ++-assoc ys [ x ] xs)
      (λ xs → isPropΠ (λ ys → trunc (xs ++ ys) (ys ++ xs)))

  record WSMon {a} (A : Type a) : Type a where
    infixr 10 _⊕_
    field
      e : A
      _⊕_ : A → A → A
      unitl : ∀ x → e ⊕ x ≡ x
      assocr : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
      comm : ∀ x y → x ⊕ y ≡ y ⊕ x
      hLevel : isSet A
  open WSMon

  record WSMonHom {a b} {A : Type a} {B : Type b} (M : WSMon A) (N : WSMon B) : Type (ℓ-max a b) where
    private
      module M = WSMon M
      module N = WSMon N
    field
      ϕ : A → B
      preserves-e : ϕ M.e ≡ N.e
      preserves-⊕ : ∀ x y → ϕ (x M.⊕ y) ≡ ϕ x N.⊕ ϕ y
  open WSMonHom

  SListWSMon : ∀ {a} {A : Type a} → WSMon (SList A)
  SListWSMon .e = []
  SListWSMon ._⊕_ = _++_
  SListWSMon .unitl xs = refl
  SListWSMon .assocr = ++-assoc
  SListWSMon .comm = ++-comm
  SListWSMon .hLevel = trunc

  η : ∀ {a} {A : Type a} → A → SList A
  η a = [ a ]

  module _ {a m} {A : Type a} {M : Type m} (M* : WSMon M) where
    private
      module M = WSMon M*
      sharp : (A → M) → SList A → M
      sharp f = SListElim.rec M
        M.e
        (λ a h → f a M.⊕ h)
        (λ x y h → sym (M.assocr (f x) (f y) h) ∙∙ ap (M._⊕ h) (M.comm (f x) (f y)) ∙∙ M.assocr (f y) (f x) h)
        M.hLevel

    [_]_♯ = sharp

    module _ (h* : WSMonHom SListWSMon M*) (f : A → M) where
      private
        module h = WSMonHom h*
        sharp-uniq : h.ϕ ∘ η ≡ f → ∀ xs → h.ϕ xs ≡ sharp f xs
        sharp-uniq p = SListElim.indProp (λ xs → h.ϕ xs ≡ sharp f xs)
          h.preserves-e
          (λ x {xs} H → h.preserves-⊕ [ x ] xs ∙ ap (M._⊕ h.ϕ xs) (funExt⁻ p x) ∙ ap (f x M.⊕_) H)
          (λ xs → M.hLevel (h.ϕ xs) (sharp f xs))

      [_]_♯-uniq = sharp-uniq


  module Mem {a} {A : Type a} where
    infix 5 _∈[_]_
    _∈[_]_ : A → isSet A →  SList A → hProp a
    x ∈[ ϕ ] xs = SListElim.rec (hProp _)
      L.⊤
      (λ a h → ((a ≡ x) , ϕ a x) L.⊔ h)
      (λ a b h → L.⊔-assoc ((a ≡ x) , ϕ a x) ((b ≡ x) , ϕ b x) h
               ∙∙ ap (L._⊔ h) (L.⊔-comm ((a ≡ x) , ϕ a x) ((b ≡ x) , ϕ b x))
               ∙∙ sym (L.⊔-assoc ((b ≡ x) , ϕ b x) ((a ≡ x) , ϕ a x) h))
      isSetHProp
      xs

  record isHead {a} {A : Type a} (ϕ : isSet A) (h : SList A → 𝟙 ⊎ A) : Type a where
    open Mem
    field
      onEmpty : h [] ≡ inl ⋆
      onCons : ∀ x xs → Σ A λ a → (h (x ∷ xs) ≡ inr a)
      isMem : ∀ x xs → ⟨ onCons x xs .fst ∈[ ϕ ] (x ∷ xs) ⟩

    -- isPropOnCons : isProp (∀ x xs → Σ A λ a → (h (x ∷ xs) ≡ inr a) × fst (a ∈[ ϕ ] (x ∷ xs)))
    -- isPropOnCons = isPropΠ2 λ { x xs (a₁ , φ) (a₂ , ϑ) →
    --   ΣPathPProp (λ a → isProp× (isSet⊎ isSetUnit ϕ (h (x ∷ xs)) (inr a)) (snd (a ∈[ ϕ ] x ∷ xs)))
    --              (isEmbedding→Inj isEmbedding-inr a₁ a₂ (sym (φ .fst) ∙ ϑ .fst)) }

    -- _⊓_ : A → A → A
    -- a ⊓ b = onCons a [ b ] .fst

    -- ⊓-comm : ∀ a b → a ⊓ b ≡ b ⊓ a
    -- ⊓-comm a b =
    --   let p : h [ a ⸴ b ] ≡ h [ b ⸴ a ] ; p = ap h (swap a b [])
    --       q : inr (onCons a [ b ] .fst) ≡ h [ a ⸴ b ] ; q = sym (onCons a [ b ] .snd .fst)
    --       r : inr (onCons b [ a ] .fst) ≡ h [ b ⸴ a ] ; r = sym (onCons b [ a ] .snd .fst)
    --   in isEmbedding→Inj isEmbedding-inr (a ⊓ b) (b ⊓ a) (q ∙∙ p ∙∙ sym r)


  -- head : ∀ {a} {A : Type a} → List A → 𝟙 ⊎ A
  -- head {A = A} = [ 𝟙+⟨ A ⟩-WSMon ] inr ♯

  -- _ : ∀ {a} {A : Type a} → head {A = A} [] ≡ inl ⋆
  -- _ = refl

  -- _ : head [ 2 ⸴ 1 ⸴ 3 ] ≡ inr 2
  -- _ = refl
