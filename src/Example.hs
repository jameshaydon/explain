{-# LANGUAGE ApplicativeDo #-}

-- | An example of using ExplainT.
module Example where

import Control.Applicative
import Control.Monad.Explain
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Bifunctor
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text hiding (group)
import Prettyprinter hiding (group)

type Username = Text

type PostID = Text

type GroupID = Text

data User = User
  { username :: Username,
    perms :: [Perm]
  }

data Group = Group
  { groupID :: GroupID,
    moderators :: [Username]
  }

data Perm = Admin | Edit
  deriving stock (Eq, Ord, Show)

instance Pretty Perm where
  pretty =
    squotes . \case
      Admin -> "admin"
      Edit -> "edit"

data Post = Post
  { postID :: PostID,
    author :: Username,
    group :: GroupID,
    content :: Text
  }

data Thing
  = ThUser Username
  | ThPost PostID
  | ThGroup (Maybe GroupID)
  | ThPerm Perm
  | ThAuthor
  | ThModerator
  | ThThe Thing
  | ThA Thing
  | ThOf Thing Thing
  deriving stock (Eq, Ord, Show)

instance Pretty Thing where
  pretty = \case
    ThUser u -> "user" <+> squotes (pretty u)
    ThPost p -> "post" <+> squotes (pretty p)
    ThGroup Nothing -> "group"
    ThGroup (Just g) -> "group" <+> squotes (pretty g)
    ThPerm p -> pretty p <+> "access"
    ThAuthor -> "author"
    ThModerator -> "moderator"
    ThThe t -> "the" <+> pretty t
    ThA t -> "a" <+> pretty t
    ThOf x y -> pretty x <+> "of" <+> pretty y

data DB = DB
  { users :: Map Username User,
    posts :: Map PostID Post,
    groups :: Map GroupID Group
  }

newtype App a = App {unApp :: ReaderT DB (ExplainT (Expl (Dual (Fact Thing))) Identity) a}
  deriving newtype
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadReader DB,
      MonadExplain (Expl (Dual (Fact Thing)))
    )

runApp :: App a -> (Expl (Dual (Fact Thing)), Maybe a)
runApp = first optimizeExpl . runIdentity . runExplainT . flip runReaderT db . unApp

runAppIO :: (Show a) => App a -> IO ()
runAppIO x = do
  let (e, res) = runApp x
  print (pretty e)
  print res

getThing :: (Ord thingID) => (DB -> Map thingID thing) -> (thingID -> Dual (Fact Thing)) -> thingID -> App thing
getThing things eNoThing thingID = do
  thing_ <- asks (Map.lookup thingID . things)
  case thing_ of
    Nothing -> failure (Custom (eNoThing thingID))
    Just thing -> pure thing

getPost :: PostID -> App Post
getPost = getThing posts (Neg . Exists . ThPost)

getGroup :: PostID -> App Group
getGroup = getThing groups (Neg . Exists . ThGroup . Just)

getUser :: Username -> App User
getUser = getThing users (Neg . Exists . ThUser)

isAuthorOf :: User -> Post -> App ()
isAuthorOf user post =
  guarded
    (author post == username user)
    (Custom (Pos (Is (ThUser (username user)) (ThOf (ThThe ThAuthor) (ThPost (postID post))))))
    ()

postGroup :: PostID -> App GroupID
postGroup postID = do
  post <- getPost postID
  success (Custom (Pos (Is (ThOf (ThThe (ThGroup Nothing)) (ThPost postID)) (ThGroup (Just (group post)))))) (group post) -- Of (ThPost postID) (ThGroup (group post))

isGroupModerator :: Username -> GroupID -> App ()
isGroupModerator username groupID = do
  group <- getGroup groupID
  guarded
    (username `elem` moderators group)
    (Custom (Pos (Is (ThUser username) (ThOf (ThThe ThModerator) (ThGroup (Just groupID))))))
    ()

moderatesGroupOfPost :: User -> PostID -> App ()
moderatesGroupOfPost user postID = do
  groupID <- postGroup postID
  isGroupModerator (username user) groupID

hasPerm :: User -> Perm -> App ()
hasPerm user perm =
  guarded
    (perm `elem` perms user)
    (Custom (Pos (Has (ThUser (username user)) (ThPerm perm))))
    ()

canEditPost :: Username -> PostID -> App ()
canEditPost username postID = do
  user <- getUser username
  post <- getPost postID
  (user `hasPerm` Edit)
    *> ( user `isAuthorOf` post
           <|> user `moderatesGroupOfPost` postID
           <|> user `hasPerm` Admin
       )

canRequestEditAccess :: Username -> PostID -> App ()
canRequestEditAccess username postID = enot (canEditPost username postID)

db :: DB
db =
  DB
    { users =
        Map.fromList
          [ ( "james",
              User
                { username = "james",
                  perms = [Edit]
                }
            )
          ],
      posts =
        Map.fromList
          [ ( "explain",
              Post
                { postID = "explain",
                  author = "julian",
                  group = "haskell",
                  content = "explain is awesome"
                }
            )
          ],
      groups =
        Map.fromList
          [ ( "haskell",
              Group
                { groupID = "haskell",
                  moderators = ["simon"]
                }
            )
          ]
    }
