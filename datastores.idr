-- from chapters 4 and 6 in Type Driven Programming with Idris
module datastores

import Data.Vect

infixr 5 |+|

data Schema = SString
            | SInt
            | (|+|) Schema Schema

SchemaType: Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x |+| y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkData
    schema: Schema
    size: Nat
    items: Vect size (SchemaType schema)

|||appends item to datastore in accordance to given schema
append : (store: DataStore) -> SchemaType (schema store) -> DataStore
append (MkData schema size items) y = MkData _ _ (addData items)
    where
        addData : Vect n (SchemaType schema) -> Vect (S n) (SchemaType schema)
        addData [] = [y]
        addData (x :: xs) = x :: (addData xs)

|||converts a schema to a string
disp : SchemaType schema -> String
disp {schema = SString} item = show item
disp {schema = SInt} item = show item
disp {schema = (x |+| y)} (lhs, rhs) = disp lhs ++ ", " ++ disp rhs

get : (store: DataStore) -> Integer -> Maybe (String, DataStore)
get store k = case integerToFin k (size store) of
                     Nothing => Just ("Out of range!\n",store)
                     Just x => Just (disp (index x (items store)) ++ "\n",store)

data Command: Schema -> Type where
    SetSchema : (newschema : Schema) -> Command schema
    Add: SchemaType schema -> Command schema
    Get: Integer -> Command schema
    Quit: Command schema


||| see parseBySchema
parsePrefix : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema, String)
parsePrefix SString str = getQuoted (unpack str)
    where
        getQuoted : List Char -> Maybe (String, String)
        getQuoted ('"' :: xs)
            = case span (/= '"') xs of
                 (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                 _ => Nothing
        getQuoted _ = Nothing

parsePrefix SInt str = case span isDigit str of
                    ("",rest) => Nothing
                    (n, rest) => Just (cast n, ltrim rest)
parsePrefix (x |+| y) str = do
                (l, rest) <- parsePrefix x str
                (r, rest') <- parsePrefix y rest
                Just ((l,r), rest')


||| parse a given string in accordance to a given schema
parseBySchema : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema)
parseBySchema schema str = case parsePrefix schema str of
                    Just (res, "") => Just res
                    Just _ => Nothing
                    Nothing => Nothing

|||parses a string into a schema
parseSchema : List String -> Maybe Schema
parseSchema ("string" :: xs) = case xs of
                    [] => Just SString
                    _ => do sch <- parseSchema xs
                            Just (SString |+| sch)
parseSchema ("int" :: xs) = case xs of
                    [] => Just SInt
                    _ => do sch <- parseSchema xs
                            Just (SInt |+| sch)
parseSchema _ = Nothing

|||see parse
parseCommand : (schema: Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "quit" "" = Just Quit
parseCommand schema "add" str = case parseBySchema schema str of
                            Nothing => Nothing
                            Just x => Just (Add x)
--parseCommand schema "size" "" = Just Size
--parseCommand schema "search" str = Just (Search str)
parseCommand schema "get" ind = case all isDigit (unpack ind) of
                            False => Nothing
                            True => Just (Get (cast ind))
parseCommand schema "schema" rest = case parseSchema (words rest) of
                             Nothing => Nothing
                             Just sch => Just (SetSchema sch)
parseCommand  _  _  _  = Nothing

|||takes a string and turns it into a command in accordance to a given schema
parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                (cmd, arg) => parseCommand schema cmd (ltrim arg)

|||given a datastore and a schema, outputs an empty datatstore with new schema if empty
setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              (S k) => Nothing

||| processes a given input and executes associated commands
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput x input = case parse (schema x) input of
                     Nothing => Just("Invalid command \n",x)
                     Just Quit => Nothing
                     --Just Size => Just (show (size x) ++ "\n",x)
                     Just (Get n) => get x n
                     Just (Add s) => Just ("ID:" ++ show (size x) ++ "\n", append x s)
                     Just (SetSchema sch) => case setSchema x sch of
                               Nothing => Just ("update failed\n",x)
                               (Just store) => Just ("OK\n", store)
                     --Just (Search s) => Just (search x s,x)
main : IO()
main = replWith (MkData SString _ []) "Command: " processInput
