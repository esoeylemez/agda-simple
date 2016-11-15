-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Fin.Core where

open import Core
open import Data.Nat
import Data.Nat.Core as Nat


data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

instance
  Fin-Number : {n : ℕ} → Number (Fin (suc n))
  Fin-Number {n} =
    record {
      Constraint = λ x → x ℕ,≤.≤ n;
      fromNat = f n
    }

    where
    f : ∀ n x {{_ : x ℕ,≤.≤ n}} → Fin (suc n)
    f n .0 {{Nat.0≤s}} = fzero
    f (suc n) (suc x) {{Nat.s≤s p}} = fsuc (f n x {{p}})

  Fin,≡ : ∀ {n} → Equiv (Fin n)
  Fin,≡ = PropEq _


fsuc-inj : ∀ {n} {x y : Fin (suc n)} → fsuc x ≡ fsuc y → x ≡ y
fsuc-inj ≡-refl = ≡-refl


fromℕ : ∀ {n} (x : ℕ) → x Nat.≤ n → Fin (suc n)
fromℕ zero p = fzero
fromℕ (suc x) (Nat.s≤s p) = fsuc (fromℕ x p)


toℕ : ∀ {n} → Fin (suc n) → ∃ (λ x → x Nat.≤ n)
toℕ fzero = zero , Nat.0≤s
toℕ {zero} (fsuc ())
toℕ {suc n} (fsuc x) with toℕ x
toℕ {suc n} (fsuc x) | x' , p = suc x' , Nat.s≤s p


embed : ∀ {n} → Fin n → Fin (suc n)
embed fzero = fzero
embed (fsuc x) = fsuc (embed x)


_≤_ : ∀ {n} (x y : Fin (suc n)) → Set _
x ≤ y = fst (toℕ x) Nat.≤ fst (toℕ y)

infix 1 _≤_

_≤?_ : ∀ {n} (x y : Fin (suc n)) → Decision (x ≤ y)
x ≤? y = fst (toℕ x) Nat.≤? fst (toℕ y)


-- Fin,≤ : ∀ {n} → TotalOrder (Fin (suc n))
-- Fin,≤ {n} =
--   record {
--     partialOrder = record {
--       Eq = Fin,≡;
--       _≤_ = _≤_;
--       antisym = antisym;
--       refl' = refl';
--       trans = λ {x} {y} {z} → trans {x} {y} {z}
--     };
--     total = total
--   }

--   where
--   not-s≤0 : ∀ {n} {x : Fin (suc n)} → not (fsuc x ≤ fzero)
--   not-s≤0 ()

--   antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
--   antisym {fzero} {fzero} p q = ≡-refl
--   antisym {fzero} {fsuc y} p q with not-s≤0 {!!}
--   antisym {fzero} {fsuc y} p q | ()
--   antisym {fsuc x} p q = {!!}

--   refl' : ∀ {x y} → x ≡ y → x ≤ y
--   refl' = {!!}

--   trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
--   trans = {!!}

--   total : ∀ x y → Either (x ≤ y) (y ≤ x)
--   total = {!!}
