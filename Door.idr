-- --Chapter 13.1.1 - 13.1.2
-- --door state machine with finite (precisely 2) states
-- --define possible states
data DoorResult = DoorJammed | OK
data DoorState = DoorClosed | DoorOpen


data DoorCmd : (ty : Type) -> (initState : DoorState) -> (handler : (ty -> DoorState)) -> Type where
    Open : DoorCmd DoorResult DoorClosed
                (\x => case x of
                    DoorJammed => DoorClosed
                    OK => DoorOpen)
    Close : DoorCmd () DoorOpen (const DoorClosed)
    RingBell : DoorCmd () DoorClosed (const DoorClosed)
    Display : String -> DoorCmd () state (const state)

    Pure : (res : ty) -> DoorCmd ty (stfn res) stfn
    (>>=) : DoorCmd a st1 st2f
        -> ((res : a) -> DoorCmd b (st2f res) st3f)
        -> DoorCmd b st1 st3f



f : DoorCmd () DoorClosed (const DoorClosed)
f =  do RingBell
        case !Open of
            OK => do
                Display "pepegers!\n"
                Close
            DoorJammed => Display "jammed\n"
