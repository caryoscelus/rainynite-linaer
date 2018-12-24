{-- GLFW.agda - some bindings to Graphics.GPipe.Context.GLFW
 -- Copyright (C) 2018 caryoscelus
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

module GLFW where

open import Data.Bool

open import Hask
import GLFW.Types as Types′
module Types = Types′
open Types

{-# FOREIGN GHC import Graphics.GPipe.Context.GLFW #-}
  
postulate
  ModifierKeys : Set

{-# COMPILE GHC ModifierKeys = type ModifierKeys #-}

MouseCallback : Set → Set
MouseCallback App =
  (button : MouseButton)
  (state : MouseButtonState)
  (mods : ModifierKeys)
  → App → App

MouseCallback′ : {M : Set} → Set → Set
MouseCallback′ {M} App =
  (modApp : (App → App) → M)
  (button : MouseButton)
  (state : MouseButtonState)
  (mods : ModifierKeys)
  → M

mouseCallbackWrap :
  ∀ {M App} → MouseCallback App → MouseCallback′ {M} App
mouseCallbackWrap f modApp button state mods =
  modApp (f button state mods)

CursorCallback : Set → Set
CursorCallback App =
  (app : App)
  (x y : Double)
  → App

CursorCallback′ : {M : Set} → Set → Set
CursorCallback′ {M} App =
  (modApp : (App → App) → M)
  (x y : Double)
  → M

cursorCallbackWrap :
  ∀ {M App} → CursorCallback App → CursorCallback′ {M} App
cursorCallbackWrap f modApp x y = modApp (λ app → f app x y)

KeyCallback : Set → Set
KeyCallback App =
  (app : App)
  (key : Key)
  (scancode : Int)
  (state : KeyState)
  (mods : ModifierKeys)
  → App

KeyCallback′ : {M : Set} → Set → Set
KeyCallback′ {M} App =
  (modApp : (App → App) → M)
  (key : Key)
  (scancode : Int)
  (state : KeyState)
  (mods : ModifierKeys)
  → M

keyCallbackWrap :
  ∀ {M App} → KeyCallback App → KeyCallback′ {M} App
keyCallbackWrap f modApp key scancode state mods = modApp
  (λ app → f app key scancode state mods)
