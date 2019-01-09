{-- test.agda - playing with agda/haskell interop
 -- Copyright (C) 2018-2019 caryoscelus
 --
 -- This program is free software: you can redistribute it and/or modify
 -- it under the terms of the GNU General Public License as published by
 -- the Free Software Foundation, either version 3 of the License, or
 -- (at your option) any later version.
 --
 -- This program is distributed in the hope that it will be useful,
 -- but WITHOUT ANY WARRANTY; without even the implied warranty of
 -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -- GNU General Public License for more details.
 --
 -- You should have received a copy of the GNU General Public License
 -- along with this program.  If not, see <http://www.gnu.org/licenses/>.
 --}

{-# OPTIONS --safe --without-K #-}

module test where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
import Data.Integer as ℤ
open import Data.Sum hiding (map)
open import Data.Product hiding (map ; zip)
import Data.Product as P
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

import IO.Primitive as Prim
import IO

open import Function

open import Hask
import GLFW
open GLFW.Types

open import NanoLens
open import GLApp

record Stroke : Set where
  constructor mkStroke
  field
    sZoom : Int
    sPoints : List Point

open Stroke

Picture = List Stroke

record AllApp : Set where
  field
    frames : List Picture

    zoomLevel : Int
    cursor : V2 Coord
    isDrawing : Bool
    
    nowFrame : ℕ
    frameCount : ℕ

    needToClearTexture : Bool

open AllApp

emptyApp : ℕ → AllApp
emptyApp nFrames = record
  { frameCount = nFrames
  ; nowFrame = 0
  ; frames = replicate nFrames []
  ; cursor = v2 (ℤ.+ 0) (ℤ.+ 0)
  ; isDrawing = false
  ; zoomLevel = I0
  ; needToClearTexture = true
  }

modifyAt : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (f : A → A) → List A → List A
modifyAt n f [] = []
modifyAt zero f (x ∷ l) = f x ∷ l
modifyAt (suc n) f (x ∷ l) = x ∷ modifyAt n f l

newShape : AllApp → AllApp
newShape app =
  let
    zl = zoomLevel app
    fi = nowFrame app
  in
    modify ፦[ frames ] (modifyAt fi (mkStroke zl [] ∷_)) app

appendShape : AllApp → AllApp
appendShape app =
  let
    xy = cursor app
    fi = nowFrame app
  in
    modify ፦[ frames ]
      (modifyAt fi (λ
       { (mkStroke z ss ∷ shapes) → mkStroke z (xy ∷ ss) ∷ shapes
       ; [] → [] -- TODO should never happen, eliminate
       }))
      app

_⟫_ : ∀ {ℓ} {A B C : Set ℓ} (F : A → B) (G : B → C) → (A → C)
_⟫_ = flip _∘′_

when′ : ∀ {ℓ} {A : Set ℓ} (cond : Bool) → (A → A) → (A → A)
when′ false _ = id
when′ true f = f

mouseCallback : GLFW.MouseCallback AllApp
mouseCallback button MouseButtonState'Pressed mods =
  set ፦[ isDrawing ] true ⟫ newShape
mouseCallback button _ mods = set ፦[ isDrawing ] false

cursorCallback : GLFW.CursorCallback AllApp
cursorCallback x y app =
  (set ፦[ cursor ] (screenToGl wh wh x y) ⟫ λ app →
  let
    draw = isDrawing app
  in
    when′ draw appendShape app) app

loopFrameLeft : ℕ → ℕ → ℕ
loopFrameLeft m zero = pred m
loopFrameLeft m (suc n) = n

loopFrameRight : ℕ → ℕ → ℕ
loopFrameRight m n
  with suc n <? m
...  | yes _ = suc n
...  | no _  = 0

keyCallback : GLFW.KeyCallback AllApp
keyCallback _ _ KeyState'Released _ = id
keyCallback Key'Equal _ _ _ =
  set ፦[ needToClearTexture ] true ⟫
  modify ፦[ zoomLevel ] Isuc
keyCallback Key'Minus _ _ _ =
  set ፦[ needToClearTexture ] true ⟫
  modify ፦[ zoomLevel ] Ipred
keyCallback Key'Left _ _ _ app =
  ( set ፦[ needToClearTexture ] true
  ⟫ modify ፦[ nowFrame ] (loopFrameLeft (frameCount app))
  ) app
keyCallback Key'Right _ _ _ app =
  ( set ፦[ needToClearTexture ] true
  ⟫ modify ፦[ nowFrame ] (loopFrameRight (frameCount app))
  ) app
keyCallback _ _ _ _ = id

pic⇒triangles : Int → Picture → List (V2 Float)
pic⇒triangles zoom = foldr addStroke []
  where
    addStroke :
      (stroke : Stroke) (vertices : List (V2 Float)) → List (V2 Float)
    addStroke stroke =
      let
        sp = sPoints stroke
        q = toZoom zoom (sZoom stroke)
        ss = zip sp (drop 1 sp)
      in
        concat (map (uncurry (drawLine q)) ss) ++_

getLast : ∀ {ℓ} {A : Set ℓ} (z : A) (xs : List A) → A
getLast z [] = z
getLast z (x ∷ xs) = getLast x xs

index : ∀ {ℓ} {A : Set ℓ} (z : A) (n : ℕ) (xs : List A) → A
index z _ [] = z
index z zero (x ∷ xs) = x
index z (suc n) (x ∷ xs) = index x n xs

module _ where
  import Data.Vec as V
  import Data.Fin as Fin

  vec-length : ∀ {ℓ n} {A : Set ℓ} → V.Vec A n → ℕ
  vec-length {_} {n} _ = n

  getAround : ∀ {ℓ} {A : Set ℓ} (z : A) (n : ℕ) (xs : List A) → A × A
  getAround z n xs
    with length xs | V.fromList xs
  ...  | .zero     | V.[] = z , z
  ...  | .(suc _)  | xs′@(_ V.∷ _) =
    let
      kk x = V.lookup (x mod (vec-length xs′)) xs′
    in
      P.map kk kk (pred n , suc n)

  v2avg : V2 Coord → V2 Coord → V2 Coord
  v2avg a b = v2
    (avgC (V2.x a) (V2.x b))
    (avgC (V2.y a) (V2.y b))

  sample-at :
    ∀ {m} (n : ℕ)
    {m≠0 : m ≡ 0 → ⊥}
    {n≠0 : False (n ≟ 0)}
    (xs : V.Vec (V2 Coord) m)
    (i : ℕ)
    → V2 Coord
  sample-at {m} n {m≠0} {n≠0} xs i =
    let
      p′ = _div_ (i * m) n {n≠0}
      p = p′ ⊓ pred m
      p-ok : p < m
      p-ok = ≤-trans
        (s≤s (m⊓n≤n p′ (pred m)))
        (≤-reflexive (m≢0⇒suc[pred[m]]≡m m≠0))
    in
      V.lookup (Fin.fromℕ≤ p-ok) xs

  doIt : List (V2 Coord) → List (V2 Coord) → List (V2 Coord)
  doIt a b
    with length a | V.fromList a | length b | V.fromList b
  ...  | .zero    | V.[]     | .zero    | V.[]         = []
  ...  | .(suc _) | _ V.∷ _  | .zero    | V.[]         = []
  ...  | .zero    | V.[]     | .(suc _) | _ V.∷ _      = []
  ...  | .(suc _) | xs@(_ V.∷ _) | .(suc _) | ys@(_ V.∷ _)     =
    let
      l = vec-length xs ⊔ vec-length ys
    in
      V.toList $
        V.map (λ n →
          v2avg
            (sample-at l {λ ()} xs n)
            (sample-at l {λ ()} ys n))
        (V.fromList $ upTo l)

-- UGH ; ignoring zoom ; ...
iStrokes : Stroke → Stroke → Stroke
iStrokes a b = modify ፦[ sPoints ] (doIt (sPoints b)) a

interpolate : Int → Picture → Picture → List (V2 Float)
interpolate zoom before after =
  pic⇒triangles zoom (map (uncurry iStrokes) (zip before after))

toTriangles′ : Int → ℕ → List Picture → Triangles
toTriangles′ zoom n frames
  with drop n frames
...  | [] = []
...  | frame ∷ tail
  with frame
...  | [] = uncurry (interpolate zoom) (getAround frame n frames)
...  | _ ∷ _ = pic⇒triangles zoom frame

toTriangles : AllApp → Triangles
toTriangles x = toTriangles′
  (zoomLevel x) -- -256
  (nowFrame x)
  (frames x)

defaultFrameCount = 24

drawApp : DrawApp AllApp
drawApp = record
  { empty = emptyApp defaultFrameCount
  ; render = toTriangles
  ; frameCount = frameCount
  ; nowFrame = nowFrame
  ; dontClearTexture = set ፦[ needToClearTexture ] false
  ; getNeedToClearTexture = needToClearTexture
  ; mouseCallback = GLFW.mouseCallbackWrap mouseCallback
  ; cursorCallback = GLFW.cursorCallbackWrap cursorCallback
  ; keyCallback = GLFW.keyCallbackWrap keyCallback
  }

main = run ∘ lift ∘ everything $ drawApp
  where open IO
