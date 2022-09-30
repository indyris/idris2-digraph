module Data.Digraph

import Data.Maybe
import Data.SortedMap
import Data.SortedSet

||| A directed graph type where vertices and edges are just ids. Operations 'do what i mean', so
||| inserting an edge will insert any mentioned vertices etc.
export
record Digraph (0 vertex : Type) (0 edge : Type) where
  constructor MkDigraph
  vertices : SortedSet vertex
  edges    : SortedMap edge (vertex, vertex)
  from     : SortedMap vertex (SortedMap vertex $ SortedSet edge)
  to       : SortedMap vertex (SortedMap vertex $ SortedSet edge)

||| A set of all vertices in the graph
export %inline
vertices : Digraph v e -> SortedSet v
vertices = (.vertices)

||| A map of all edges in the graph
export %inline
edges : Digraph v e -> List (e, v, v)
edges = map (\(x,(y,z)) => (x, y, z)) . Data.SortedMap.toList . (.edges)

||| Is the vertex with the provided label present?
export
hasVertex : v -> Digraph v e -> Bool
hasVertex v = contains v . (.vertices) 

||| Is the edge with the provided label present?
export
hasEdge : e -> Digraph v e -> Bool
hasEdge e = isJust . lookup e . (.edges) 

||| Look up an edge
export
edge : e -> Digraph v e -> Maybe (v, v)
edge e = lookup e . (.edges)

||| The set of edges from a vertex
export
from : v -> Digraph v e -> Maybe (SortedMap v (SortedSet e))
from key = lookup key . (.from)

||| The set of edges to a vertex
export
to : v -> Digraph v e -> Maybe (SortedMap v (SortedSet e))
to key = lookup key . (.to)

||| The set of edges from a vertex to another
export
fromTo : v -> v -> Digraph v e -> Maybe (SortedSet e)
fromTo f t g = from f g >>= (lookup t)

||| Like `from` but returns a possibly empty set instead of a `Maybe`.
export
from' : Ord v => v -> Digraph v e -> SortedMap v (SortedSet e)
from' key = fromMaybe empty . from key

||| Like `to` but returns a possibly empty set instead of a `Maybe`.
export

  to' : Ord v => v -> Digraph v e -> SortedMap v (SortedSet e)
to' key = fromMaybe empty . to key

||| Like `fromTo` but returns a possibly empty set instead of a `Maybe`.
export
fromTo' : Ord e => v -> v -> Digraph v e -> SortedSet e
fromTo' f t = fromMaybe empty . fromTo f t

||| Edges from a vertex
export
edgesFrom : Ord v => Ord e => v -> Digraph v e -> (SortedSet e)
edgesFrom key = foldl union empty . values . from' key

||| Edges to a vertex
export
edgesTo : Ord v => Ord e => v -> Digraph v e -> (SortedSet e)
edgesTo key = foldl union empty . values . to' key

||| Edges from or to a vertex
export
edgesWith : Ord v => Ord e => v -> Digraph v e -> (SortedSet e)
edgesWith k g = edgesFrom k g `union` edgesTo k g

||| True if there are no edges to a vertex
export
isRoot : Ord v => Ord e => v -> Digraph v e -> Bool
isRoot v = isNothing . to v

||| True if there are no edges from a vertex
export
isTerminal : Ord v => Ord e => v -> Digraph v e -> Bool
isTerminal v = isNothing . from v


-- we now take a diversion for a bunch of private functions that weren't much fun to write.

deleteEdgeIn
  :  (Eq v, Ord v)
  => (Eq e, Ord e)
  => e -> v -> v
  -> SortedMap v (SortedMap v (SortedSet e))
  -> SortedMap v (SortedMap v (SortedSet e))
deleteEdgeIn e o i outer =
  case lookup o outer of
    Nothing => outer
    Just inner =>
      case lookup i inner of
        Nothing => outer
        Just set =>
          let set = delete e set in
          if set /= empty then insert o (insert i set inner) outer -- update
          else let inner = delete i inner in
            if inner == empty
            then delete o outer                      -- prune us out of the entire toplevel
            else insert o (insert i set inner) outer -- prune just this destination

deleteEdgeFrom : (Eq v, Ord v) => (Eq e, Ord e) => e -> v -> v -> Digraph v e -> Digraph v e
deleteEdgeFrom e f t = { from $= deleteEdgeIn e f t }

deleteEdgeTo : (Eq v, Ord v) => (Eq e, Ord e) => e -> v -> v -> Digraph v e -> Digraph v e
deleteEdgeTo e f t = { to $= deleteEdgeIn e t f }

deleteEdgeFromTo : (Eq v, Ord v) => (Eq e, Ord e) => e -> v -> v -> Digraph v e -> Digraph v e
deleteEdgeFromTo e f t = { from $= deleteEdgeIn e f t, to $= deleteEdgeIn e t f }

deleteEdgesIn
  :  (Eq v, Ord v) => (Eq e, Ord e) => v -> v
  -> SortedMap v (SortedMap v (SortedSet e))
  -> SortedMap v (SortedMap v (SortedSet e))
deleteEdgesIn o i outer =
  case lookup o outer of
    Nothing => outer
    Just inner =>
      let inner = delete i inner in
      if inner == empty
      then delete o outer       -- prune us out of the entire toplevel
      else insert o inner outer -- prune just this destination

deleteEdgesFrom : (Eq v, Ord v) => (Eq e, Ord e) => v -> v -> Digraph v e -> Digraph v e
deleteEdgesFrom f t = { from $= deleteEdgesIn f t }

deleteEdgesTo : (Eq v, Ord v) => (Eq e, Ord e) => v -> v -> Digraph v e -> Digraph v e
deleteEdgesTo f t = { to $= deleteEdgesIn t f }

addIn
  :  (Eq v, Ord v) => (Eq e, Ord e)
  => e -> v -> v
  -> SortedMap v (SortedMap v (SortedSet e))
  -> SortedMap v (SortedMap v (SortedSet e))
addIn e o i outer =
  let inner = fromMaybe empty (lookup o outer)
      set = fromMaybe empty (lookup i inner)
      inner = insert i set inner
  in insert o inner outer

-- and back to the public api.

||| Deletes an edge by name
export
deleteEdge : (Eq v, Ord v) => (Eq e, Ord e) => e -> Digraph v e -> Digraph v e
deleteEdge e g = case edge e g of
  Just (f,t) => { edges $= delete e } (deleteEdgeFromTo e f t g)
  Nothing => g

||| Deletes all edges from `from` to `to`.
export
deleteEdges : (Eq v, Ord v) => (Eq e, Ord e) => (from : v) -> (to : v) -> Digraph v e -> Digraph v e
deleteEdges f t g = foldl (flip deleteEdge) g (fromTo' f t g)

||| Deletes all edges from `from`.
export
deleteAllEdgesFrom : (Eq v, Ord v) => (Eq e, Ord e) => v -> Digraph v e -> Digraph v e
deleteAllEdgesFrom f g = foldl (flip deleteEdge) g (edgesFrom f g)

||| Deletes all edges to `to`.
export
deleteAllEdgesTo : (Eq v, Ord v) => (Eq e, Ord e) => v -> Digraph v e -> Digraph v e
deleteAllEdgesTo t g = foldl (flip deleteEdge) g (edgesTo t g)

||| Deletes all edges to or from `to`.
export
deleteAllEdges : (Eq v, Ord v) => (Eq e, Ord e) => v -> Digraph v e -> Digraph v e
deleteAllEdges t g = foldl (flip deleteEdge) g (edgesWith t g)

||| Deletes a vertex.
export
deleteVertex : (Eq v, Ord v) => (Eq e, Ord e) => v -> Digraph v e -> Digraph v e
deleteVertex v = { vertices $= delete v} . deleteAllEdges v

||| The empty graph
export %inline
empty : Ord v => Ord e => Digraph v e
empty = MkDigraph empty empty empty empty

||| Adds a vertex.
export
addVertex : (Eq v, Ord v) => (Eq e, Ord e) => v -> Digraph v e -> Digraph v e
addVertex v = { vertices $= insert v }

||| Adds an edge, creating `from` and `to` if necessary
export
addEdge : (Eq v, Ord v) => (Eq e, Ord e) => e -> (from : v) -> (to : v) -> Digraph v e -> Digraph v e
addEdge e f t =
  { edges $= insert e (f, t), from $= addIn e f t, to $= addIn e t f }
  . addVertex f . addVertex t . deleteEdge e
