--
import Data.Vect
import System

-- sumType : (inputs : Nat) -> Type -> Type
-- sumType Z t = t
-- sumType (S k) t = (next : t) -> sumType k t
--
-- summation : (inputs : Nat) -> (accum : Int) -> sumType inputs Int
-- summation Z accum = accum
-- summation (S k) accum = \next => summation k (accum + next)
--
-- genericSum : Num addable => (inputs : Nat) -> addable -> sumType inputs addable
-- genericSum Z accum = accum
-- genericSum (S k) accum = \next => genericSum k (accum + next)

||| types of formats
data Format = |||terminating format
              End
            | ||| numeric format (%d)
              Number Format
            | ||| string formt (%s)
              Str Format
            | ||| literal
              Lit String Format
            | ||| chracter format (%c)
              Chr Format
            | ||| float format (%f)
              Flt Format

printf_type : Format -> Type
printf_type End = String
printf_type (Number fmt) = Int -> printf_type fmt
printf_type (Flt fmt) = Double -> printf_type fmt
printf_type (Str fmt) = String -> printf_type fmt
printf_type (Chr fmt) = Char -> printf_type fmt
printf_type (Lit x fmt) = printf_type fmt

printf' : (format : Format) -> (accum : String) -> printf_type format
printf' End accum = accum
printf' (Number fmt) accum = \i => printf' fmt (accum ++ show i)
printf' (Flt fmt) accum = \f => printf' fmt (accum ++ show f)
printf' (Str fmt) accum = \s => printf' fmt (accum ++ s)
printf' (Chr fmt) accum = \c => printf' fmt (accum ++ cast c)
printf' (Lit s fmt) accum = printf' fmt (accum ++ s)

strToFormat : List Char -> Format
strToFormat [] = End
strToFormat ('%' :: 'd' :: xs) = Number (strToFormat xs)
strToFormat ('%' :: 'f' :: xs) = Flt (strToFormat xs)
strToFormat ('%' :: 's' :: xs) = Str (strToFormat xs)
strToFormat ('%' :: 'c' :: xs) = Chr (strToFormat xs)
strToFormat ('%' :: xs) = Lit "%" (strToFormat xs)
strToFormat ( x  :: xs) = case strToFormat xs of
                               Lit str fmt => Lit (strCons x str) fmt
                               format => Lit (strCons x "") format



printf : (fmt: String) -> printf_type (strToFormat (unpack fmt))
printf fmt = printf' _ ""
