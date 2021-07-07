--chapter 12.1
module TreeLabel

import Control.Monad.State

%access public export

||| binary tree implementation
data Tree a = ||| empty node
              Empty
            | ||| non-empty tree node with two children and 1 contained value
              Node (Tree a) a (Tree a)

{-
                    Alice
                /         \
            Fred          Bob
         /      \           \
      Jim    Sheila         Eve
-}
|||a tree
testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                (Node Empty "Sheila" Empty)) "Alice"
           (Node Empty "Bob" (Node Empty "Eve" Empty))


|||flattens tree to list
flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right


|||labels a tree using (stream, tree) pair to hold current state
naivelabel : Tree a -> Tree (Integer, a)
naivelabel tree = snd $ treeLabelWith [1..] tree where
    treeLabelWith : Stream b -> Tree a -> (Stream b, Tree (b, a))
    treeLabelWith xs Empty = (xs, Empty)
    treeLabelWith xs (Node l v r) = let (lbt :: lbleft, llabelled) = treeLabelWith xs l
                                        (lbsRight, rlabelled)      = treeLabelWith lbleft r
                                    in  (lbsRight, Node llabelled (lbt, v) rlabelled)

|||labels a tree using state monad
label : Tree a -> Tree (Integer, a)
label tree = evalState (treeLabelWith tree) [1..] where
    treeLabelWith : Tree a -> State (Stream ltype) (Tree (ltype, a))
    treeLabelWith Empty = pure Empty
    treeLabelWith (Node l v r)
        = do left           <- treeLabelWith l --perform op on left subtree
             (this :: rest) <- get             --get resulting state
             put rest                          --modify current state
             right          <- treeLabelWith r --perform op on right subtree with new state
             pure (Node left (this, v) right)  --put it all together

--exercises
--1
update : (s -> s) -> State s ()
update f = put (f !get)

increase : Nat -> State Nat ()
increase k = update (+k)

--2
countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase 1
countEmpty (Node l v r) = do le <- countEmpty l
                             countEmpty r

--3
incFst : State (Nat, Nat) ()
incFst = update (\(a,b) => (a + 1, b))

incSnd : State (Nat, Nat) ()
incSnd = update (\(a,b) => (a, b + 1))

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = incFst
countEmptyNode (Node l _ r) = do countEmptyNode l
                                 incSnd
                                 countEmptyNode r

--4
