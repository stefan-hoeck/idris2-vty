module Graphics.Vty.Attributes.Color

import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

||| Abstract data type representing a color.
|||
||| Currently the foreground and background color are specified as points
||| in either a:
|||
|||  * 16 color palette. Where the first 8 colors are equal to the 8
|||  colors of the ISO 6429 (ANSI) 8 color palette and the second 8
|||  colors are bright/vivid versions of the first 8 colors.
|||
|||  * 240 color palette. This palette is a regular sampling of the full
|||  RGB colorspace for the first 224 colors. The remaining 16 colors is
|||  a greyscale palette.
|||
||| The 8 ISO 6429 (ANSI) colors are as follows:
|||
|||      * black (0)
|||
|||      * red (1)
|||
|||      * green (2)
|||
|||      * yellow (3)
|||
|||      * blue (4)
|||
|||      * magenta (5)
|||
|||      * cyan (6)
|||
|||      * white (7)
|||
||| The mapping from points in the 240 color palette to colors actually
||| displayable by the terminal depends on the number of colors the
||| terminal claims to support. Which is usually determined by the
||| terminfo "colors" property. If this property is not being accurately
||| reported then the color reproduction will be incorrect.
|||
||| If the terminal reports <= 16 colors then the 240 color palette
||| points are only mapped to the 8 color palette. I'm not sure of
||| the RGB points for the "bright" colors which is why they are not
||| addressable via the 240 color palette.
|||
||| If the terminal reports > 16 colors then the 240 color palette
||| points are mapped to the nearest points in a ("color count" - 16)
||| subsampling of the 240 color palette.
|||
||| All of this assumes the terminals are behaving similarly to xterm and
||| rxvt when handling colors. And that the individual colors have not
||| been remapped by the user. There may be a way to verify this through
||| terminfo but I don't know it.
|||
||| Seriously, terminal color support is INSANE.
public export
data Color : Type where
  ISOColor : Bits8 -> Color
  Color240 : Bits8 -> Color
  RGBColor : (r,g,b : Bits8) -> Color

%runElab derive "Color" [Show,Eq]

public export
data ColorMode : Type where
  NoColor      : ColorMode
  ColorMode8   : ColorMode
  ColorMode16  : ColorMode
  ColorMode240 : Bits8 -> ColorMode
  FullColor    : ColorMode

%runElab derive "ColorMode" [Show,Eq]

export
black, red, green, yellow, blue, magenta, cyan, white : Color
black  = ISOColor 0
red    = ISOColor 1
green  = ISOColor 2
yellow = ISOColor 3
blue   = ISOColor 4
magenta= ISOColor 5
cyan   = ISOColor 6
white  = ISOColor 7

export
brightBlack, brightRed, brightGreen, brightYellow : Color

export
brightBlue, brightMagenta, brightCyan, brightWhite : Color

brightBlack  = ISOColor 8
brightRed    = ISOColor 9
brightGreen  = ISOColor 10
brightYellow = ISOColor 11
brightBlue   = ISOColor 12
brightMagenta= ISOColor 13
brightCyan   = ISOColor 14
brightWhite  = ISOColor 15

||| Create a color value from RGB values in the 0..255 range inclusive.
||| No transformation of the input values is done; a color is created
||| directly from the RGB values specified, unlike the 'srgbColor' and
||| 'color240' functions.
export
linearColor : Cast i Bits8 => i -> i -> i -> Color
linearColor r g b = RGBColor (cast r) (cast g) (cast b)

||| Given RGB values in the range 0..255 inclusive, create a color
||| using the sRGB transformation described at
|||
||| https://en.wikipedia.org/wiki/SRGB#The_reverse_transformation
export
srgbColor : Cast i Bits8 => i -> i -> i -> Color

||| See `rgbColor`
export
color240 : Cast i Bits8 => i -> i -> i -> Color

||| Create a Vty 'Color' (in the 240 color set) from an RGB triple.
||| This is a synonym for 'color240'. This function is lossy in the sense
||| that we only internally support 240 colors but the #RRGGBB format
||| supports 256^3 colors.
export %inline
rgbColor : Cast i Bits8 => i -> i -> i -> Color
rgbColor = color240

||| Create a RGB triple from a value in the Color240 set.
export
color240CodeToRGB : Bits8 -> Maybe (Bits8, Bits8, Bits8)

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

%inline shrink : Cast i Bits8 => i -> Double
shrink n = cast (cast {to = Bits8} n) / 255.0

%inline gamma : Double -> Double
gamma u =
  if u <= 0.04045 then u/12.92 else pow 2.4 ((u + 0.055) / 1.055)

%inline expand : Double -> Bits8
expand n = cast (255.0 * n)

convert : Cast i Bits8 => i -> Bits8
convert = expand . gamma . shrink

srgbColor r g b = RGBColor (convert r) (convert g) (convert b)

simple : Bits8 -> Bits8
simple 0 = 0
simple c = if c <= 95 then 1 else ((c - 16) `div` 40)

-- | Create a value in the Color240 set from an RGB triple. This maps
-- the input arguments to an entry in the 240-color palette depicted at:
--
-- https://rich.readthedocs.io/en/stable/appendix/colors.html
rgbColorToColor240 : (r,g,b : Bits8) -> Bits8
rgbColorToColor240   8   8   8 = 216
rgbColorToColor240  18  18  18 = 217
rgbColorToColor240  28  28  28 = 218
rgbColorToColor240  38  38  38 = 219
rgbColorToColor240  48  48  48 = 220
rgbColorToColor240  58  58  58 = 221
rgbColorToColor240  68  68  68 = 222
rgbColorToColor240  78  78  78 = 223
rgbColorToColor240  88  88  88 = 224
rgbColorToColor240  98  98  98 = 225
rgbColorToColor240 108 108 108 = 226
rgbColorToColor240 118 118 118 = 227
rgbColorToColor240 128 128 128 = 228
rgbColorToColor240 138 138 138 = 229
rgbColorToColor240 148 148 148 = 230
rgbColorToColor240 158 158 158 = 231
rgbColorToColor240 168 168 168 = 232
rgbColorToColor240 178 178 178 = 233
rgbColorToColor240 188 188 188 = 234
rgbColorToColor240 198 198 198 = 235
rgbColorToColor240 208 208 208 = 236
rgbColorToColor240 218 218 218 = 237
rgbColorToColor240 228 228 228 = 238
rgbColorToColor240 238 238 238 = 239
rgbColorToColor240 r   g   b   = 36 * simple r + 6 * simple g + simple b


color240CodeToRGB 0   = Just (0, 0, 0)
color240CodeToRGB 1   = Just (0, 0, 95)
color240CodeToRGB 2   = Just (0, 0, 135)
color240CodeToRGB 3   = Just (0, 0, 175)
color240CodeToRGB 4   = Just (0, 0, 215)
color240CodeToRGB 5   = Just (0, 0, 255)
color240CodeToRGB 6   = Just (0, 95, 0)
color240CodeToRGB 7   = Just (0, 95, 95)
color240CodeToRGB 8   = Just (0, 95, 135)
color240CodeToRGB 9   = Just (0, 95, 175)
color240CodeToRGB 10  = Just (0, 95, 215)
color240CodeToRGB 11  = Just (0, 95, 255)
color240CodeToRGB 12  = Just (0, 135, 0)
color240CodeToRGB 13  = Just (0, 135, 95)
color240CodeToRGB 14  = Just (0, 135, 135)
color240CodeToRGB 15  = Just (0, 135, 175)
color240CodeToRGB 16  = Just (0, 135, 215)
color240CodeToRGB 17  = Just (0, 135, 255)
color240CodeToRGB 18  = Just (0, 175, 0)
color240CodeToRGB 19  = Just (0, 175, 95)
color240CodeToRGB 20  = Just (0, 175, 135)
color240CodeToRGB 21  = Just (0, 175, 175)
color240CodeToRGB 22  = Just (0, 175, 215)
color240CodeToRGB 23  = Just (0, 175, 255)
color240CodeToRGB 24  = Just (0, 215, 0)
color240CodeToRGB 25  = Just (0, 215, 95)
color240CodeToRGB 26  = Just (0, 215, 135)
color240CodeToRGB 27  = Just (0, 215, 175)
color240CodeToRGB 28  = Just (0, 215, 215)
color240CodeToRGB 29  = Just (0, 215, 255)
color240CodeToRGB 30  = Just (0, 255, 0)
color240CodeToRGB 31  = Just (0, 255, 95)
color240CodeToRGB 32  = Just (0, 255, 135)
color240CodeToRGB 33  = Just (0, 255, 175)
color240CodeToRGB 34  = Just (0, 255, 215)
color240CodeToRGB 35  = Just (0, 255, 255)
color240CodeToRGB 36  = Just (95, 0, 0)
color240CodeToRGB 37  = Just (95, 0, 95)
color240CodeToRGB 38  = Just (95, 0, 135)
color240CodeToRGB 39  = Just (95, 0, 175)
color240CodeToRGB 40  = Just (95, 0, 215)
color240CodeToRGB 41  = Just (95, 0, 255)
color240CodeToRGB 42  = Just (95, 95, 0)
color240CodeToRGB 43  = Just (95, 95, 95)
color240CodeToRGB 44  = Just (95, 95, 135)
color240CodeToRGB 45  = Just (95, 95, 175)
color240CodeToRGB 46  = Just (95, 95, 215)
color240CodeToRGB 47  = Just (95, 95, 255)
color240CodeToRGB 48  = Just (95, 135, 0)
color240CodeToRGB 49  = Just (95, 135, 95)
color240CodeToRGB 50  = Just (95, 135, 135)
color240CodeToRGB 51  = Just (95, 135, 175)
color240CodeToRGB 52  = Just (95, 135, 215)
color240CodeToRGB 53  = Just (95, 135, 255)
color240CodeToRGB 54  = Just (95, 175, 0)
color240CodeToRGB 55  = Just (95, 175, 95)
color240CodeToRGB 56  = Just (95, 175, 135)
color240CodeToRGB 57  = Just (95, 175, 175)
color240CodeToRGB 58  = Just (95, 175, 215)
color240CodeToRGB 59  = Just (95, 175, 255)
color240CodeToRGB 60  = Just (95, 215, 0)
color240CodeToRGB 61  = Just (95, 215, 95)
color240CodeToRGB 62  = Just (95, 215, 135)
color240CodeToRGB 63  = Just (95, 215, 175)
color240CodeToRGB 64  = Just (95, 215, 215)
color240CodeToRGB 65  = Just (95, 215, 255)
color240CodeToRGB 66  = Just (95, 255, 0)
color240CodeToRGB 67  = Just (95, 255, 95)
color240CodeToRGB 68  = Just (95, 255, 135)
color240CodeToRGB 69  = Just (95, 255, 175)
color240CodeToRGB 70  = Just (95, 255, 215)
color240CodeToRGB 71  = Just (95, 255, 255)
color240CodeToRGB 72  = Just (135, 0, 0)
color240CodeToRGB 73  = Just (135, 0, 95)
color240CodeToRGB 74  = Just (135, 0, 135)
color240CodeToRGB 75  = Just (135, 0, 175)
color240CodeToRGB 76  = Just (135, 0, 215)
color240CodeToRGB 77  = Just (135, 0, 255)
color240CodeToRGB 78  = Just (135, 95, 0)
color240CodeToRGB 79  = Just (135, 95, 95)
color240CodeToRGB 80  = Just (135, 95, 135)
color240CodeToRGB 81  = Just (135, 95, 175)
color240CodeToRGB 82  = Just (135, 95, 215)
color240CodeToRGB 83  = Just (135, 95, 255)
color240CodeToRGB 84  = Just (135, 135, 0)
color240CodeToRGB 85  = Just (135, 135, 95)
color240CodeToRGB 86  = Just (135, 135, 135)
color240CodeToRGB 87  = Just (135, 135, 175)
color240CodeToRGB 88  = Just (135, 135, 215)
color240CodeToRGB 89  = Just (135, 135, 255)
color240CodeToRGB 90  = Just (135, 175, 0)
color240CodeToRGB 91  = Just (135, 175, 95)
color240CodeToRGB 92  = Just (135, 175, 135)
color240CodeToRGB 93  = Just (135, 175, 175)
color240CodeToRGB 94  = Just (135, 175, 215)
color240CodeToRGB 95  = Just (135, 175, 255)
color240CodeToRGB 96  = Just (135, 215, 0)
color240CodeToRGB 97  = Just (135, 215, 95)
color240CodeToRGB 98  = Just (135, 215, 135)
color240CodeToRGB 99  = Just (135, 215, 175)
color240CodeToRGB 100 = Just (135, 215, 215)
color240CodeToRGB 101 = Just (135, 215, 255)
color240CodeToRGB 102 = Just (135, 255, 0)
color240CodeToRGB 103 = Just (135, 255, 95)
color240CodeToRGB 104 = Just (135, 255, 135)
color240CodeToRGB 105 = Just (135, 255, 175)
color240CodeToRGB 106 = Just (135, 255, 215)
color240CodeToRGB 107 = Just (135, 255, 255)
color240CodeToRGB 108 = Just (175, 0, 0)
color240CodeToRGB 109 = Just (175, 0, 95)
color240CodeToRGB 110 = Just (175, 0, 135)
color240CodeToRGB 111 = Just (175, 0, 175)
color240CodeToRGB 112 = Just (175, 0, 215)
color240CodeToRGB 113 = Just (175, 0, 255)
color240CodeToRGB 114 = Just (175, 95, 0)
color240CodeToRGB 115 = Just (175, 95, 95)
color240CodeToRGB 116 = Just (175, 95, 135)
color240CodeToRGB 117 = Just (175, 95, 175)
color240CodeToRGB 118 = Just (175, 95, 215)
color240CodeToRGB 119 = Just (175, 95, 255)
color240CodeToRGB 120 = Just (175, 135, 0)
color240CodeToRGB 121 = Just (175, 135, 95)
color240CodeToRGB 122 = Just (175, 135, 135)
color240CodeToRGB 123 = Just (175, 135, 175)
color240CodeToRGB 124 = Just (175, 135, 215)
color240CodeToRGB 125 = Just (175, 135, 255)
color240CodeToRGB 126 = Just (175, 175, 0)
color240CodeToRGB 127 = Just (175, 175, 95)
color240CodeToRGB 128 = Just (175, 175, 135)
color240CodeToRGB 129 = Just (175, 175, 175)
color240CodeToRGB 130 = Just (175, 175, 215)
color240CodeToRGB 131 = Just (175, 175, 255)
color240CodeToRGB 132 = Just (175, 215, 0)
color240CodeToRGB 133 = Just (175, 215, 95)
color240CodeToRGB 134 = Just (175, 215, 135)
color240CodeToRGB 135 = Just (175, 215, 175)
color240CodeToRGB 136 = Just (175, 215, 215)
color240CodeToRGB 137 = Just (175, 215, 255)
color240CodeToRGB 138 = Just (175, 255, 0)
color240CodeToRGB 139 = Just (175, 255, 95)
color240CodeToRGB 140 = Just (175, 255, 135)
color240CodeToRGB 141 = Just (175, 255, 175)
color240CodeToRGB 142 = Just (175, 255, 215)
color240CodeToRGB 143 = Just (175, 255, 255)
color240CodeToRGB 144 = Just (215, 0, 0)
color240CodeToRGB 145 = Just (215, 0, 95)
color240CodeToRGB 146 = Just (215, 0, 135)
color240CodeToRGB 147 = Just (215, 0, 175)
color240CodeToRGB 148 = Just (215, 0, 215)
color240CodeToRGB 149 = Just (215, 0, 255)
color240CodeToRGB 150 = Just (215, 95, 0)
color240CodeToRGB 151 = Just (215, 95, 95)
color240CodeToRGB 152 = Just (215, 95, 135)
color240CodeToRGB 153 = Just (215, 95, 175)
color240CodeToRGB 154 = Just (215, 95, 215)
color240CodeToRGB 155 = Just (215, 95, 255)
color240CodeToRGB 156 = Just (215, 135, 0)
color240CodeToRGB 157 = Just (215, 135, 95)
color240CodeToRGB 158 = Just (215, 135, 135)
color240CodeToRGB 159 = Just (215, 135, 175)
color240CodeToRGB 160 = Just (215, 135, 215)
color240CodeToRGB 161 = Just (215, 135, 255)
color240CodeToRGB 162 = Just (215, 175, 0)
color240CodeToRGB 163 = Just (215, 175, 95)
color240CodeToRGB 164 = Just (215, 175, 135)
color240CodeToRGB 165 = Just (215, 175, 175)
color240CodeToRGB 166 = Just (215, 175, 215)
color240CodeToRGB 167 = Just (215, 175, 255)
color240CodeToRGB 168 = Just (215, 215, 0)
color240CodeToRGB 169 = Just (215, 215, 95)
color240CodeToRGB 170 = Just (215, 215, 135)
color240CodeToRGB 171 = Just (215, 215, 175)
color240CodeToRGB 172 = Just (215, 215, 215)
color240CodeToRGB 173 = Just (215, 215, 255)
color240CodeToRGB 174 = Just (215, 255, 0)
color240CodeToRGB 175 = Just (215, 255, 95)
color240CodeToRGB 176 = Just (215, 255, 135)
color240CodeToRGB 177 = Just (215, 255, 175)
color240CodeToRGB 178 = Just (215, 255, 215)
color240CodeToRGB 179 = Just (215, 255, 255)
color240CodeToRGB 180 = Just (255, 0, 0)
color240CodeToRGB 181 = Just (255, 0, 95)
color240CodeToRGB 182 = Just (255, 0, 135)
color240CodeToRGB 183 = Just (255, 0, 175)
color240CodeToRGB 184 = Just (255, 0, 215)
color240CodeToRGB 185 = Just (255, 0, 255)
color240CodeToRGB 186 = Just (255, 95, 0)
color240CodeToRGB 187 = Just (255, 95, 95)
color240CodeToRGB 188 = Just (255, 95, 135)
color240CodeToRGB 189 = Just (255, 95, 175)
color240CodeToRGB 190 = Just (255, 95, 215)
color240CodeToRGB 191 = Just (255, 95, 255)
color240CodeToRGB 192 = Just (255, 135, 0)
color240CodeToRGB 193 = Just (255, 135, 95)
color240CodeToRGB 194 = Just (255, 135, 135)
color240CodeToRGB 195 = Just (255, 135, 175)
color240CodeToRGB 196 = Just (255, 135, 215)
color240CodeToRGB 197 = Just (255, 135, 255)
color240CodeToRGB 198 = Just (255, 175, 0)
color240CodeToRGB 199 = Just (255, 175, 95)
color240CodeToRGB 200 = Just (255, 175, 135)
color240CodeToRGB 201 = Just (255, 175, 175)
color240CodeToRGB 202 = Just (255, 175, 215)
color240CodeToRGB 203 = Just (255, 175, 255)
color240CodeToRGB 204 = Just (255, 215, 0)
color240CodeToRGB 205 = Just (255, 215, 95)
color240CodeToRGB 206 = Just (255, 215, 135)
color240CodeToRGB 207 = Just (255, 215, 175)
color240CodeToRGB 208 = Just (255, 215, 215)
color240CodeToRGB 209 = Just (255, 215, 255)
color240CodeToRGB 210 = Just (255, 255, 0)
color240CodeToRGB 211 = Just (255, 255, 95)
color240CodeToRGB 212 = Just (255, 255, 135)
color240CodeToRGB 213 = Just (255, 255, 175)
color240CodeToRGB 214 = Just (255, 255, 215)
color240CodeToRGB 215 = Just (255, 255, 255)
color240CodeToRGB 216 = Just (8, 8, 8)
color240CodeToRGB 217 = Just (18, 18, 18)
color240CodeToRGB 218 = Just (28, 28, 28)
color240CodeToRGB 219 = Just (38, 38, 38)
color240CodeToRGB 220 = Just (48, 48, 48)
color240CodeToRGB 221 = Just (58, 58, 58)
color240CodeToRGB 222 = Just (68, 68, 68)
color240CodeToRGB 223 = Just (78, 78, 78)
color240CodeToRGB 224 = Just (88, 88, 88)
color240CodeToRGB 225 = Just (98, 98, 98)
color240CodeToRGB 226 = Just (108, 108, 108)
color240CodeToRGB 227 = Just (118, 118, 118)
color240CodeToRGB 228 = Just (128, 128, 128)
color240CodeToRGB 229 = Just (138, 138, 138)
color240CodeToRGB 230 = Just (148, 148, 148)
color240CodeToRGB 231 = Just (158, 158, 158)
color240CodeToRGB 232 = Just (168, 168, 168)
color240CodeToRGB 233 = Just (178, 178, 178)
color240CodeToRGB 234 = Just (188, 188, 188)
color240CodeToRGB 235 = Just (198, 198, 198)
color240CodeToRGB 236 = Just (208, 208, 208)
color240CodeToRGB 237 = Just (218, 218, 218)
color240CodeToRGB 238 = Just (228, 228, 228)
color240CodeToRGB 239 = Just (238, 238, 238)
color240CodeToRGB _   = Nothing

color240 r g b = Color240 (rgbColorToColor240 (cast r) (cast g) (cast b))
