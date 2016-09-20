-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Mod where

open import Core
open import Data.Int.Core hiding (module Props)
import Data.Int.Core as ℤ
open import Data.Nat.Core using (ℕ)
import Data.Nat.Core as ℕ


private module ℤP = ℤ.Props


ModEq : ℕ → Equiv ℤ
ModEq n =
  record {
    _≈_ = _≈_;
    refl = λ {x} → 0 , ℤP.+-right-inv x;
    sym = λ {x} {y} → sym' x y;
    trans = λ {x} {y} {z} → trans' x y z
  }

  where
  infix 4 _≈_

  _≈_ : ℤ → ℤ → Set
  x ≈ y = ∃ (λ k → x - y ≡ k * pos n)

  sym' : ∀ x y → x ≈ y → y ≈ x
  sym' x y (k , p) =
    neg k ,
    (begin
      y - x           || sym (ℤP.neg-flip x y) ::
      neg (x - y)     || cong neg p ::
      neg (k * pos n) || sym (ℤP.*-assoc -1 k (pos n)) ::
      neg k * pos n
    qed)

    where
    open Equiv (PropEq ℤ)

  trans' : ∀ x y z → x ≈ y → y ≈ z → x ≈ z
  trans' x y z (k1 , p1) (k2 , p2) =
    k1 + k2 ,
    (begin
      x - z                   || cong (x +_) (sym (ℤP.+-left-id (neg z))) ::
      x + (0 - z)             || cong (λ a → x + (a - z)) (sym (ℤP.+-left-inv y)) ::
      x + (neg y + y - z)     || cong (x +_) (ℤP.+-assoc (neg y) y (neg z)) ::
      x + (neg y + (y - z))   || sym (ℤP.+-assoc x (neg y) (y + neg z)) ::
      x + neg y + (y - z)     || cong2 _+_ p1 p2 ::
      k1 * pos n + k2 * pos n || sym (ℤP.*-+-right-dist k1 k2 (pos n)) ::
      (k1 + k2) * pos n
    qed)

    where
    open Equiv (PropEq ℤ)


module Props (n : ℕ) where
  open Equiv (ModEq n) using (_≈_)
  open Equiv (PropEq ℤ) hiding (_≈_)

  +-cong : ∀ {x1 x2 y1 y2} → x1 ≈ x2 → y1 ≈ y2 → x1 + y1 ≈ x2 + y2
  +-cong {x1} {x2} {y1} {y2} (k1 , p1) (k2 , p2) =
    k1 + k2 ,
    (begin
      x1 + y1 - (x2 + y2)   || ℤP.+-assoc x1 y1 _ ::
      x1 + (y1 - (x2 + y2)) ||
      cong (x1 +_) (
        y1 - (x2 + y2)         || cong (y1 +_) (ℤP.*-+-left-dist -1 x2 y2) ::
        y1 + (neg x2 + neg y2) || sym (ℤP.+-assoc y1 (neg x2) (neg y2)) ::
        (y1 + neg x2 + neg y2) || cong (_+ neg y2) (ℤP.+-comm y1 (neg x2)) ::
        neg x2 + y1 + neg y2   || ℤP.+-assoc (neg x2) y1 _ ::
        neg x2 + (y1 + neg y2)
      qed) ::
      x1 + (neg x2 + (y1 + neg y2)) || sym (ℤP.+-assoc x1 (neg x2) _) ::
      x1 - x2 + (y1 - y2)           || cong2 _+_ p1 p2 ::
      k1 * pos n + k2 * pos n       || sym (ℤP.*-+-right-dist k1 k2 (pos n)) ::
      (k1 + k2) * pos n
    qed)
