{-- Strokes.hs - stroke representation
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

{-# LANGUAGE
  NoMonomorphismRestriction,
  TemplateHaskell,
  ScopedTypeVariables,
  TypeFamilies,
  LambdaCase,
  GADTs,
  FlexibleContexts
  #-}

module Strokes where

import Graphics.GPipe -- TODO
import Data.Label

type Coord = Integer
type Point = V2 Coord
type Container a = [ a ]

data Stroke = Stroke
  { _sZoom :: Int
  , _sPoints :: [Point]
  }

mkLabel ''Stroke

type Picture = Container Stroke
