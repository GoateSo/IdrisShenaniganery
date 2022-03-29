--chapter 13.1
--exercise 2
data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S k) (k)

    Pure : ty -> GuessCmd ty state state

    (>>=) : GuessCmd a state1 state2 ->
            (a -> GuessCmd b state2 state3) ->
            GuessCmd b state1 state3



a : GuessCmd () 3 0
a = do Try 20
       Try 15
       Try 10
       Pure ()

-- --should error
-- b : GuessCmd () 0 0
-- b = do Try 1
--        Pure ()


--exercise 3
data Matter = Solid | Liquid | Gas

data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt : MatterCmd () Solid Liquid
    Condense : MatterCmd () Gas Liquid
    Freeze : MatterCmd () Liquid Solid
    Boil : MatterCmd () Liquid Gas

    Bind : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) -> MatterCmd b s1 s

namespace MatterBind
    (>>=) : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) -> MatterCmd b s1 s
    (>>=) = Bind

iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze

-- --should error
-- overMelt : MatterCmd () Solid Gas
-- overMelt = do Melt
--               Melt
