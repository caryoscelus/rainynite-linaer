{-- T.hs - some imperative opengl mess
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


module Main where

import Debug.Trace (traceShowId)
import Data.Maybe
import Data.Word (Word32)
import Graphics.GPipe
import qualified Graphics.GPipe.Context.GLFW as GLFW
import Data.IORef
import Control.Monad.IO.Class
import Control.Monad
import Data.Label
import Data.Label.Derive

import GL
import Util

type Coord = Integer
type Point = V2 Coord

data Stroke = Stroke
  { sZoom :: Int
  , sPoints :: [Point]
  }

type Picture = [Stroke]

toTriangles :: Int -> Picture -> [V2 Float]
toTriangles zoom = foldr addStroke []
  where
    addStroke stroke vertices =
      let
        sp = sPoints stroke
        ss = zip sp (drop 1 sp)
        q = toZoom zoom (sZoom stroke)
      in
        (ss >>= drawLine q) <> vertices

zoomStep = 32
toZoom to from = 2 ** (fromIntegral (to - from) / zoomStep)

drawLine :: Double -> (Point, Point) -> [V2 Float]
drawLine _ (a , b) | a == b = []
drawLine q (a' , b') =
  let
    tt = realToFrac . (* q) . fromIntegral
    toQ = \(V2 x y) -> V2 (tt x) (tt y)
    a = toQ a'
    b = toQ b'
    dt = perp (signorm (a - b)) / 256
  in
    [ a-dt    , a+dt
              , b+dt
    , a-dt      
    , b-dt    , b+dt
    ]

v2to4 :: Num i => V2 i -> V4 i
v2to4 (V2 x y) = V4 x y 0 1

wh = 512


data DrawApp = DrawApp
  { _frameCount :: Int
  , _nowFrame :: Int
  , _frames :: [Picture]
  
  , _cursor :: V2 Coord
  , _isDrawing :: Bool
      
  , _zoomLevel :: Int
  
  , _needToClearTexture :: Bool
  }

mkLabel ''DrawApp

emptyApp :: Int -> DrawApp
emptyApp nFrames = DrawApp
  { _frameCount = nFrames
  , _nowFrame = 0
  , _frames = replicate nFrames []

  , _cursor = V2 0 0
  , _isDrawing = False

  , _zoomLevel = 0

  , _needToClearTexture = True
  }

defaultFrameCount = 24
defaultEmptyApp = emptyApp defaultFrameCount

requestClearTexture :: DrawApp -> DrawApp
requestClearTexture = set needToClearTexture True

clearedTexture :: DrawApp -> DrawApp
clearedTexture = set needToClearTexture False

newShape :: DrawApp -> DrawApp
newShape app =
  let
    zl = get zoomLevel app
    fi = get nowFrame app
  in
    modify frames (modifyAt fi (Stroke zl [] :)) app


appendShape :: DrawApp -> DrawApp
appendShape app =
  let
    xy = get cursor app
    fi = get nowFrame app
  in
    modify frames
      (modifyAt fi
       (\(Stroke z ss : shapes) -> Stroke z (xy:ss) : shapes))
      app

screenToGl :: Int -> Int -> Double -> Double -> V2 Coord
screenToGl w h x y = V2
  (- fromIntegral w `div` 2 + floor x)
  (fromIntegral h `div` 2 - floor y)

main :: IO ()
main = runContextT GLFW.defaultHandleConfig $ do
  let nFrames = defaultFrameCount

  app <- liftIO $ newIORef (emptyApp nFrames)

  frameTextures <-
    sequence . replicate nFrames $ newTexture2D RGB8 (V2 wh wh) 1

  let
    void = minBound :: Word32
    clearTex t = do
      writeTexture2D t 0 0 (V2 wh wh) (repeat (V3 void void void))
  
  let wCfg = (GLFW.defaultWindowConfig "rainynite-linaer")
        { GLFW.configWidth = wh , GLFW.configHeight = wh }
  win <- newWindow (WindowFormatColor RGB8) wCfg

  let
    penColor = V3 0.5 0.5 0.5
    bgColor  = V3 0.0 0.0 0.0
    allColors = V3 True True True

  brushTexShader <- compileShader (singleColorOnTextureShader wh wh)
  texShader <- compileShader (singleTextureOnWindowShader win wh wh)

  GLFW.setMouseButtonCallback win . pure $ \button state mods -> do
    let
      pressed = state == GLFW.MouseButtonState'Pressed
    liftIO $ modifyIORef app (set isDrawing pressed)
    when pressed $ modifyIORef app newShape


  GLFW.setCursorPosCallback win . pure $ \x y -> do
    liftIO $ modifyIORef app (set cursor (screenToGl wh wh x y))
    draw <- liftIO $ get isDrawing <$> readIORef app
    when draw $ modifyIORef app appendShape

  GLFW.setKeyCallback win . pure $ \key i state mods -> do
    when (state /= GLFW.KeyState'Released) $ do
      modifyIORef app requestClearTexture
      case key of
        GLFW.Key'Equal -> modifyIORef app (modify zoomLevel succ)
        GLFW.Key'Minus -> modifyIORef app (modify zoomLevel pred)
        GLFW.Key'Left -> do
          nFrames <- get frameCount <$> readIORef app
          modifyIORef app $ modify nowFrame ((`mod` nFrames) . pred)
        GLFW.Key'Right -> do
          nFrames <- get frameCount <$> readIORef app
          modifyIORef app $ modify nowFrame ((`mod` nFrames) . succ)
        -- GLFW.Key'Z -> modifyIORef shapes (drop 1)
        _ -> pure ()

  wholeScreenBuff :: Buffer os (B2 Float) <- newBuffer 4
  writeBuffer wholeScreenBuff 0
    [ V2   0    0
    , V2   0    1
    , V2   1    1
    , V2   1    0
    ]

  foreverTil (fromMaybe False <$> GLFW.windowShouldClose win) $ do
    fi <- liftIO $ get nowFrame <$> readIORef app
    picture <- fmap (!! fi) . liftIO $ get frames <$> readIORef app
    zl <- liftIO $ get zoomLevel <$> readIORef app
    haveToClear <- liftIO $ get needToClearTexture <$> readIORef app

    let nowTex = frameTextures !! fi

    when haveToClear $ clearTex nowTex
    liftIO $ modifyIORef app clearedTexture

    let
      lines = toTriangles (zl - 256) picture

    lineBuff :: Buffer os (B4 Float, B3 Float) <- newBuffer (length lines)
    unless (lines == []) $
      writeBuffer lineBuff 0 (fmap (\xy -> (v2to4 xy , penColor)) lines)

    -- render frame to texture
    -- TODO: don't re-render when not needed
    render $ do
      vertexArray <- newVertexArray lineBuff
      let brushTriangles = toPrimitiveArray TriangleList vertexArray
      img <- getTexture2DImage nowTex 0
      brushTexShader (OnTexture img brushTriangles)

    -- put that onto window
    render $ do
      clearWindowColor win bgColor
      wholeScreen <- newVertexArray wholeScreenBuff
      let wholeScreenTriangles = toPrimitiveArray TriangleFan wholeScreen
      texShader (RenderTexture wholeScreenTriangles nowTex)

    swapWindowBuffers win

    pure ()
