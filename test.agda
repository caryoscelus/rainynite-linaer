module test where

open import Data.Empty
open import Data.Unit
open import Data.Bool

import IO.Primitive as Prim
import IO

open import Function

{-# FOREIGN GHC
  import T
  #-}

module fclabels where
  {-# FOREIGN GHC
      import Data.Label
    #-}
  
  postulate
    _፦_ : (F A : Set) → Set
    set : {A F : Set} (lens : F ፦ A) → A → F → F
    get : {A F : Set} (lens : F ፦ A) → F → A

  {-# COMPILE GHC _፦_ = type (:->) #-}
  {-# COMPILE GHC set = \_ _ -> set #-}
  {-# COMPILE GHC get = \_ _ -> get #-}

open fclabels

module GLFW where
  {-# FOREIGN GHC import Graphics.GPipe.Context.GLFW #-}
  
  postulate
    MouseButton ModifierKeys MouseButtonState : Set
    MouseButtonState'Pressed : MouseButtonState
    _==_ : (x y : MouseButtonState) → Bool

  {-# COMPILE GHC MouseButton = type MouseButton #-}
  {-# COMPILE GHC ModifierKeys = type ModifierKeys #-}
  {-# COMPILE GHC MouseButtonState = type MouseButtonState #-}
  {-# COMPILE GHC MouseButtonState'Pressed = MouseButtonState'Pressed #-}
  {-# COMPILE GHC _==_ = (==) #-}

postulate
  DrawApp : Set
  isDrawing : DrawApp ፦ Bool
  newShape : DrawApp → DrawApp

{-# COMPILE GHC DrawApp = type DrawApp #-}
{-# COMPILE GHC isDrawing = isDrawing #-}
{-# COMPILE GHC newShape = newShape #-}

MouseCallback : {M : Set} → Set
MouseCallback {M} =
  (modApp : (DrawApp → DrawApp) → M)
  (button : GLFW.MouseButton)
  (state : GLFW.MouseButtonState)
  (mods : GLFW.ModifierKeys)
  → M

postulate
  everything : MouseCallback {Prim.IO ⊤} → Prim.IO ⊤

{-# COMPILE GHC
    everything = T.everything 
  #-}

_⟫_ : ∀ {ℓ} {A B C : Set ℓ} (F : A → B) (G : B → C) → (A → C)
_⟫_ = flip _∘′_

when′ : ∀ {ℓ} {A : Set ℓ} (cond : Bool) → (A → A) → (A → A)
when′ false _ = id
when′ true f = f

mouseCallback : ∀ {M} → MouseCallback {M}
mouseCallback modApp button state mods =
  let
    pressed = state GLFW.== GLFW.MouseButtonState'Pressed
  in
    modApp (set isDrawing pressed ⟫ when′ pressed newShape)


main = run $ do
  lift $ everything mouseCallback
  where
    open IO
