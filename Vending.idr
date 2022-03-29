--13.1.3 -> 13.1.4
VendState : Type
VendState = (Nat, Nat)

--valid inputs
data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type -> (init : VendState) -> (new : VendState) -> Type where
    -- core ops
    AddCoin  : MachineCmd () (coins, chocs) (S coins, chocs)
    Vend     : MachineCmd () (S coins, S chocs) (coins, chocs)
    GetCoins : MachineCmd () (coins, chocs) (Z, chocs)
    Refill   : (bars : Nat) -> MachineCmd () (Z, chocs) (Z, chocs + bars)
    --helpers
    Display  : String -> MachineCmd () st st
    GetInput : MachineCmd (Maybe Input) st st
    --combinators
    Pure : t -> MachineCmd t st st
    (>>=) : MachineCmd a st1 st2 ->
            (a -> MachineCmd b st2 st3) ->
            MachineCmd b st1 st3


--
data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

namespace MachineDo
    (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
    (>>=) = Do


mutual
    vend : MachineIO (coins, chocs)
    vend {coins = (S k)} {chocs = (S j)}
         = do Vend
              Display "Enjoy"
              machineLoop
    vend {coins = Z}
         = do Display "insert a coin"
              machineLoop
    vend {chocs = Z}
         = do Display "out of order"
              machineLoop

    refill : (num : Nat) -> MachineIO (coins, chocs)
    refill {coins = Z} num = do Refill num
                                machineLoop
    refill _ = do Display "cannot refill, coins are in the machine"
                  machineLoop

    machineLoop : MachineIO (coins, chocs)
    machineLoop = do Just x <- GetInput
                            | Nothing => do Display "invalid input"
                                            machineLoop
                     case x of
                         COIN => do AddCoin
                                    machineLoop
                         VEND => vend
                         CHANGE => do GetCoins
                                      Display "Change Recieved"
                                      machineLoop
                         (REFILL k) => refill k
