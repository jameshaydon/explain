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

data Fact
  = IsAuthor Username PostID
  | IsModerator Username GroupID
  | HasPerm Username Perm
  | NoPostWithID PostID
  | NoUserWithUsername Username
  | NoGroupWithID GroupID
  | PostOfGroup PostID GroupID
  deriving stock (Eq, Ord, Show)

instance Pretty (Dual Fact) where
  pretty = \case
    Pos (IsAuthor u p) -> squotes (pretty u) <+> "authored post" <+> squotes (pretty p)
    Neg (IsAuthor u p) -> squotes (pretty u) <+> "isn't the author of post" <+> squotes (pretty p)
    Pos (IsModerator u g) -> squotes (pretty u) <+> "moderates" <+> squotes (pretty g)
    Neg (IsModerator u g) -> squotes (pretty u) <+> "isn't a moderator of" <+> squotes (pretty g)
    Pos (HasPerm u p) -> squotes (pretty u) <+> "has" <+> pretty p <+> "access"
    Neg (HasPerm u p) -> squotes (pretty u) <+> "does not have" <+> pretty p <+> "access"
    Pos (NoPostWithID i) -> "There is no post with ID" <> colon <+> squotes (pretty i)
    Neg (NoPostWithID i) -> "Post" <+> squotes (pretty i) <+> "exists"
    Pos (NoUserWithUsername u) -> "No user with username" <> colon <+> squotes (pretty u)
    Neg (NoUserWithUsername u) -> "User" <+> squotes (pretty u) <+> "exists"
    Pos (NoGroupWithID g) -> "No group with ID" <> colon <+> squotes (pretty g)
    Neg (NoGroupWithID g) -> "group" <+> squotes (pretty g) <+> "exists"
    Pos (PostOfGroup p g) -> "Post" <+> squotes (pretty p) <+> "belongs to group" <+> squotes (pretty g)
    Neg (PostOfGroup p g) -> "Post" <+> squotes (pretty p) <+> "does not belong to group" <+> squotes (pretty g)

data DB = DB
  { users :: Map Username User,
    posts :: Map PostID Post,
    groups :: Map GroupID Group
  }

newtype App a = App {unApp :: ReaderT DB (ExplainT (Expl (Dual Fact)) Identity) a}
  deriving newtype
    ( Functor,
      Applicative,
      Alternative,
      Monad,
      MonadReader DB,
      MonadExplain (Expl (Dual Fact))
    )

runApp :: App a -> (Expl (Dual Fact), Maybe a)
runApp = first optimizeExpl . runIdentity . runExplainT . flip runReaderT db . unApp

runAppIO :: (Show a) => App a -> IO ()
runAppIO x = do
  let (e, res) = runApp x
  print (pretty e)
  print res

getThing :: (Ord thingID) => (DB -> Map thingID thing) -> (thingID -> Fact) -> thingID -> App thing
getThing things eNoThing thingID = do
  thing_ <- asks (Map.lookup thingID . things)
  case thing_ of
    Nothing -> failure (Custom (Pos (eNoThing thingID)))
    Just thing -> pure thing

getPost :: PostID -> App Post
getPost = getThing posts NoPostWithID

getGroup :: PostID -> App Group
getGroup = getThing groups NoGroupWithID

getUser :: Username -> App User
getUser = getThing users NoUserWithUsername

isAuthorOf :: User -> Post -> App ()
isAuthorOf user post =
  guarded
    (author post == username user)
    (Custom (Pos (IsAuthor (username user) (postID post))))
    ()

postGroup :: PostID -> App GroupID
postGroup postID = do
  post <- getPost postID
  success (Custom (Pos (PostOfGroup postID (group post)))) (group post)

isGroupModerator :: Username -> GroupID -> App ()
isGroupModerator username groupID = do
  group <- getGroup groupID
  guarded
    (username `elem` moderators group)
    (Custom (Pos (IsModerator username groupID)))
    ()

moderatesGroupOfPost :: User -> PostID -> App ()
moderatesGroupOfPost user postID = do
  groupID <- postGroup postID
  isGroupModerator (username user) groupID

hasPerm :: User -> Perm -> App ()
hasPerm user perm =
  guarded
    (perm `elem` perms user)
    (Custom (Pos (HasPerm (username user) perm)))
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
                  perms = []
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
