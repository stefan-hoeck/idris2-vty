module Graphics.Vty.Image

import Data.String
import Graphics.Text.Width
import Graphics.Vty.Attributes
import public Graphics.Vty.Image.Internal

%default total

public export
record Region where
  constructor MkRegion
  width  : Nat
  height : Nat

||| An area of the picture's background (See 'Background').
export
backgroundFill : (cols, rows : Nat) -> Image
backgroundFill w@(S _) h@(S _) = BGFill w h
backgroundFill _       _       = Empty

||| Combines two images horizontally. This is an alias for 'horizJoin'.
export %inline
(<|>) : Image -> Image -> Image
(<|>) = horizJoin

||| Compose any number of images together horizontally, with the first
||| in the list being leftmost.
export %inline
horizCat : List Image -> Image
horizCat = foldl horizJoin Empty

||| Compose any number of images vertically, with the first in the list
||| being topmost.
export %inline
vertCat : List Image -> Image
vertCat = foldl vertJoin Empty

||| Make an 'Image' from a string value. The text value should be
||| sanitized of escape sequences (ASCII 27) and carriage returns;
||| otherwise layout and attribute problems may result.
export %inline
text : Attr -> String -> Image
text a txt = HorizText a txt (strWidth txt) (length txt)

||| Make an image from a single unicode character.
export %inline
char : Attr -> Char -> Image
char a c = HorizText a (singleton c) (charWidth c) 1

export
FromString Image where fromString = text defAttr

||| Make an image filling a region with the specified character.
|||
||| If either the width or height are less than or equal to 0, then
||| the result is the empty image.
export
charFill : Attr -> Char -> (width, height : Nat) -> Image
charFill a c w@(S _) h@(S _) =
  let txt := String.replicate w c
      dw  := charWidth c * w
   in vertCat $ replicate h (HorizText a txt dw w)
charFill _ _ _ _             = Empty

||| Pad the given image. This adds background character fills to the
||| left, top, right, bottom.
export
pad : (left, top, right, bottom : Nat) -> Image -> Image
pad 0 0 0 0 i  = i
pad l t r b i0 =
  let h  := height i0
      w  := width i0 + l + r
      i1 := BGFill l h <|> i0 <|> BGFill r h
   in BGFill w t <+> i1 <+> BGFill w b

||| Crop an image's width. If the image's width is less than or equal
||| to the specified width then this operation has no effect. Otherwise
||| the image is cropped from the left.
export
cropLeft : Nat -> Image -> Image
cropLeft 0 _     = Empty
cropLeft _ Empty = Empty
cropLeft w (Crop i ls ts ow oh) =
  let d := ow `minus` w
   in Crop i (ls + d) ts (ow `minus` d) oh
cropLeft w i     =
  let iw := width i
   in if iw <= w then i else Crop i (iw `minus` w) 0 w (height i)

||| Crop an image's width. If the image's width is less than or equal
||| to the specified width then this operation has no effect. Otherwise
||| the image is cropped from the right.
export
cropRight : Nat -> Image -> Image
cropRight 0 _     = Empty
cropRight _ Empty = Empty
cropRight w (Crop i ls ts ow oh) = Crop i ls ts (min ow w) oh
cropRight w i     = if w > width i then i else Crop i 0 0 w (height i)

||| Crop an image's height. If the image's height is less than or equal
||| to the specified height then this operation has no effect. Otherwise
||| the image is cropped from the top.
export
cropTop : Nat -> Image -> Image
cropTop 0 _     = Empty
cropTop _ Empty = Empty
cropTop h (Crop i ls ts ow oh) =
  let d := oh `minus` h
   in Crop i ls (ts + d) ow (oh `minus` d)
cropTop h i     =
  let ih := height i
   in if ih <= h then i else Crop i 0 (ih `minus` h) (width i) h

||| Crop an image's height. If the image's height is less than or equal
||| to the specified height then this operation has no effect. Otherwise
||| the image is cropped from the bottom.
export
cropBottom : Nat -> Image -> Image
cropBottom 0 _     = Empty
cropBottom h Empty = Empty
cropBottom h (Crop i ls ts ow oh) = Crop i ls ts ow $ min oh h
cropBottom h i     = if h > height i then i else Crop i 0 0 (width i) h

||| Translates an image by padding or cropping its left side.
export
translateX : Integer -> Image -> Image
translateX 0 i = i
translateX x i =
  let True  := x < 0 | False => BGFill (cast x) (height i) <|> i
      d     := cast {to = Nat} (abs x)
      w     := width i
      False := d > w | True => Empty
   in cropLeft (w `minus` d) i

export
translateY : Integer -> Image -> Image
translateY 0 i = i
translateY x i =
  let True  := x < 0 | False => BGFill (width i) (cast x) <+> i
      d     := cast {to = Nat} (abs x)
      h     := height i
      False := d > h | True => Empty
   in cropTop (h `minus` d) i

||| Translates an image by padding or cropping the left and top.
|||
||| If translation offsets are negative then the image is cropped.
export %inline
translate : (horiz, vert : Integer) -> Image -> Image
translate x y = translateX x . translateY y

||| Ensure an image is no larger than the provided size. If the image
||| is larger then crop the right or bottom.
|||
||| This is equivalent to a vertical crop from the bottom followed by
||| horizontal crop from the right.
export %inline
crop : (width, height : Nat) -> Image -> Image
crop w@(S _) h@(S _) i = cropBottom h $ cropRight w i
crop _       _       _ = Empty

||| Resize the width. Pads and crops as required to assure the given
||| display width. This is biased to pad/crop on the right.
export
resizeWidth : Nat -> Image -> Image
resizeWidth w i =
  case w `compare` width i of
    LT => cropRight w i
    EQ => i
    GT => i <|> BGFill (w `minus` width i) (height i)

||| Resize the height. Pads and crops as required to assure the given
||| display height. This is biased to pad/crop on the bottom.
export
resizeHeight : Nat -> Image -> Image
resizeHeight h i =
  case h `compare` height i of
    LT => cropBottom h i
    EQ => i
    GT => i <+> BGFill (width i) (h `minus` height i)


||| Generic resize. Pads and crops are added to ensure that the
||| resulting image matches the specified dimensions. This is biased to
||| pad/crop the right and bottom.
export %inline
resize : Nat -> Nat -> Image -> Image
resize w h = resizeHeight h . resizeWidth w
