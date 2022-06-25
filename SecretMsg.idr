-- chapter 14.2 exercise 1
data Access  = LoggedIn | LoggedOut
data PwdCheck = Correct | Incorrect

data ShellCmd : (ty : Type) -> (istate : Access) -> (handler : (ty -> Access)) -> Type where
    Password : String -> ShellCmd PwdCheck LoggedOut
        (\x => case x of
            Correct => LoggedIn
            Incorrect => LoggedOut)
    LogOut : ShellCmd () LoggedIn (const LoggedOut)
    GetSecret : ShellCmd String LoggedIn (const LoggedIn)

    PutStr : String -> ShellCmd () st (const st)
    Pure : (res : ty) -> ShellCmd ty (st_fn res) st_fn
    (>>=) : ShellCmd a s1 sf2
        -> ((res : a) -> ShellCmd b (sf2 res) sf3)
        -> ShellCmd b s1 sf3

session : ShellCmd () LoggedOut (const LoggedOut)
session = do
    Correct <- Password "wurzel" | Incorrect => PutStr "Wrong password"
    msg <- GetSecret
    PutStr ("secret code: " ++ msg ++ "\n")
    LogOut
