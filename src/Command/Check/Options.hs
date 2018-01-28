module Command.Check.Options where

import Data.List.NonEmpty(NonEmpty)
import qualified Syntax.Concrete.Scoped as Scoped

data Options = Options
  { inputFiles :: NonEmpty FilePath
  , verbosity :: Int
  , logFile :: Maybe FilePath
  , probePos :: Maybe Scoped.ProbePos
  } deriving (Show)
