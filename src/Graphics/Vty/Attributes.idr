module Graphics.Vty.Attributes

import Data.Bits
import Derive.Prelude
import public Graphics.Vty.Attributes.Color

%default total
%language ElabReflection

||| Styles are represented as an 8 bit word. Each bit in the word is 1
||| if the style attribute assigned to that bit should be applied and 0
||| if the style attribute should not be applied.
public export
0 Style : Type
Style = Bits8

--  (The invisible, protect, and altcharset display attributes some
--  terminals support are not supported via VTY.)
export %inline
standout, underline, reverseVideo, blink, dim, bold, italic, strikethrough : Style
standout        = 0x01
underline       = 0x02
reverseVideo    = 0x04
blink           = 0x08
dim             = 0x10
bold            = 0x20
italic          = 0x40
strikethrough   = 0x80

export %inline
defaultStyleMask : Style
defaultStyleMask = 0x00

||| The style and color attributes can either be the terminal defaults.
||| Or be equivalent to the previously applied style. Or be a specific
||| value.
public export
data MaybeDefault : Type -> Type where
  Default     : MaybeDefault t
  KeepCurrent : MaybeDefault t
  SetTo       : (val : t) -> MaybeDefault t

%runElab derive "MaybeDefault" [Show,Eq]

||| A display attribute defines the Color and Style of all the
||| characters rendered after the attribute is applied.
|||
||| At most 256 colors, picked from a 240 and 16 color palette, are
||| possible for the background and foreground. The 240 colors and
||| 16 colors are points in different palettes. See Color for more
||| information.
public export
record Attr where
  constructor MkAttr
  style      : MaybeDefault Style
  foreground : MaybeDefault Color
  background : MaybeDefault Color

%runElab derive "Attr" [Show,Eq]

||| Specifies the display attributes such that the final style and
||| color values do not depend on the previously applied display
||| attribute. The display attributes can still depend on the terminal's
||| default colors (unfortunately).
public export
record FixedAttr where
  constructor MkFixedAttr
  style      : Style
  foreground : Maybe Color
  background : Maybe Color

%runElab derive "FixedAttr" [Show,Eq]

export
styleMask : Attr -> Bits8
styleMask a =
  case a.style of
    Default     => 0
    KeepCurrent => 0
    SetTo v     => v

||| true if the given Style value has the specified Style set.
export %inline
hasStyle : Style -> Style -> Bool
hasStyle s bitMask = ( s .&. bitMask ) /= 0

||| Set the foreground color of an `Attr'.
export %inline
withForeground : Attr -> Color -> Attr
withForeground attr c = { foreground := SetTo c } attr

||| Set the background color of an `Attr'.
export %inline
withBackground : Attr -> Color -> Attr
withBackground attr c = { background := SetTo c } attr

||| Add the given style attribute
export
withStyle : Attr -> Style -> Attr
withStyle attr 0 = attr
withStyle attr s = { style := SetTo (styleMask attr .|. s) } attr

||| Sets the style, background color and foreground color to the
||| default values for the terminal. There is no easy way to determine
||| what the default background and foreground colors are.
export
defAttr : Attr
defAttr = MkAttr Default Default Default

||| Keeps the style, background color and foreground color that was
||| previously set. Used to override some part of the previous style.
|||
||| EG: current_style `withForeground` brightMagenta
|||
||| Would be the currently applied style (be it underline, bold, etc) but
||| with the foreground color set to brightMagenta.
export
currentAttr : Attr
currentAttr = MkAttr KeepCurrent KeepCurrent KeepCurrent
