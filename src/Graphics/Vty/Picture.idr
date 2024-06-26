module Graphics.Vty.Picture

import Derive.Prelude
import Graphics.Vty.Attributes
import Graphics.Vty.Image

%default total
%language ElabReflection

||| A picture can be configured to hide the cursor or to show the
||| cursor at the specified character position.
|||
||| There is not a 1:1 map from character positions to a row and column
||| on the screen due to characters that take more than 1 column.
public export
data Cursor : Type where
    ||| Hide the cursor
    NoCursor : Cursor

    ||| Set the terminal's cursor position without displaying a cursor
    ||| character. This is important for accessibility with screen
    ||| readers where a cursor position needs to be reported but we may
    ||| not want to show a block cursor in that location for cosmetic
    ||| reasons. The boolean argument indicates whether the positioning
    ||| should be absolute as with 'AbsoluteCursor' ('True') or logical
    ||| as with 'Cursor' ('False').
    PositionOnly : (absolute : Bool) -> (col,row : Nat) -> Cursor

    ||| Show the cursor at the given logical column accounting for
    ||| character width in the presence of multi-column characters.
    Visible : (absolute : Bool) -> (col,row : Nat) -> Cursor

%runElab derive "Cursor" [Show,Eq]

||| A 'Picture' has a background pattern. The background is either:
|||
||| * ClearBackground, which shows the layer below or is blank if the
|||   bottom layer
||| * A character and a display attribute
|||
||| If the display attribute used previously should be used for a
||| background fill then use `currentAttr` for the background attribute.
public export
data Background : Type where
  ClearBG : Background
  CharBG  : Char -> Attr -> Background

%runElab derive "Background" [Show,Eq]

||| These can be constructed directly or using `picForImage`.
public export
record Picture where
  constructor MkPicture
  cursor     : Cursor
  layers     : List Image
  background : Background

%runElab derive "Picture" [Show,Eq]

||| A picture with no cursor, background or image layers.
export
emptyPicture : Picture
emptyPicture = MkPicture NoCursor [] ClearBG

||| Add an 'Image' as the top-most layer of a 'Picture'.
export
addToTop : Picture -> Image -> Picture
addToTop p i = {layers $= (i::)} p

||| Add an 'Image' as the bottom-most layer of a 'Picture'.
export
addToBottom : Picture -> Image -> Picture
addToBottom p i = {layers $= (++ [i])} p

||| Create a picture from the given image. The picture will not have a
||| displayed cursor and no background pattern (ClearBackground) will be
||| used.
export
picForImage : Image -> Picture
picForImage i = {layers := [i]} emptyPicture

||| Create a picture with the given layers, top-most first.
|||
||| The picture will not have a displayed cursor and no background
||| pattern (ClearBackgroun) will be used.
export
picForLayers : List Image -> Picture
picForLayers is = {layers := is} emptyPicture

||| Return the top-most 'Image' layer for a picture or `Empty` if
||| there are no layers.
|||
||| This is provided for compatibility with applications that do not use
||| more than a single layer.
export
picImage : Picture -> Image
picImage p =
  case p.layers of
    h::_ => h
    []   => Empty
