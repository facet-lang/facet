{-# LANGUAGE GADTs #-}
module Facet.Effect.CallStack
( call
, pushCallStack
, Stack
, callStack
, CallStack(..)
) where

import           Control.Algebra
import           Data.Text (Text, pack)
import qualified Facet.Source.Reference as Ref
import qualified Facet.Span as Span
import qualified GHC.Stack as Stack

call :: (Stack.HasCallStack, Has CallStack sig m) => m a -> m a
call m = case Stack.getCallStack Stack.callStack of
  (label, loc):_ -> pushCallStack (pack label) (Ref.Reference (Just (Stack.srcLocFile loc)) (Span.Span (Span.Pos (Stack.srcLocStartLine loc) (Stack.srcLocStartCol loc)) (Span.Pos (Stack.srcLocEndLine loc) (Stack.srcLocEndCol loc)))) m
  _              -> m

pushCallStack :: Has CallStack sig m => Text -> Ref.Reference -> m a -> m a
pushCallStack l s m = send (Push l s m)

type Stack = [(Text, Ref.Reference)]

callStack :: Has CallStack sig m => m Stack
callStack = send CallStack

data CallStack m a where
  Push :: Text -> Ref.Reference -> m a -> CallStack m a
  CallStack :: CallStack m Stack
