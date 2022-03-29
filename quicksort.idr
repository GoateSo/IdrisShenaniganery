import Data.Vect

%default total

splitVectOn : Ord a => (pivot : a) -> Vect n a ->
              (k1 : Nat ** k2 : Nat ** (k1 + k2 = n, Vect k1 a, Vect k2 a))
splitVectOn pivot [] = (0 ** 0 ** (Refl, [], []))
splitVectOn pivot (x :: xs) =
    let (k1 ** k2 ** (prf, ys, zs)) = splitVectOn pivot xs in
    if x <= pivot then
        (S k1 ** k2 ** (cong prf , x :: ys , zs))
    else let eq1 = sym $ plusSuccRightSucc k1 k2
             eq2 = cong {f = S} prf in
        (k1 ** S k2 ** (trans eq1 eq2 , ys , x :: zs))


qsort : Ord a => Vect n a -> Vect n a
qsort [] = []
qsort list @ (x :: xs) =
    let (k1 ** k2 ** (prf, ys, zs)) = splitVectOn x xs
        p1 = sym $ cong {f = S} prf
        p2 = plusSuccRightSucc k1 k2
        left = qsort $ assert_smaller list ys
        right = qsort $ assert_smaller list zs
        res = left ++ (x :: right)
        prf' = trans p1 p2
    in rewrite prf' in res
