# Forced placement of the first physical edges

Let `T` be a Leech tree (of any order for which the displayed distances
exist), and call an edge of weight `j` the *physical `j`-edge*, denoted `e_j`,
when it exists.  The following gives an exhaustive local split through
distance 6.  It is a structural lemma, not a witness or a nonexistence result.

## Path-composition rule

Every physical edge weight is itself a pair distance, so physical edge
weights are distinct.  If the unique pair at distance `k` is not an edge, its
path has at least two edges, with distinct positive integer weights summing to
`k`.  Conversely, whenever a path of physical edges has total weight `k`, its
endpoints already realize distance `k`, so no physical `k`-edge can exist.

Thus `e_1` and `e_2` always exist.  The only distinct positive multi-edge
composition of 3 is `1+2`.  Consequently:

- if `e_1,e_2` are adjacent, their two outer endpoints realize 3, so `e_3`
  does not exist;
- if `e_1,e_2` are disjoint, no path of total 3 exists, so `e_3` does exist.

For a physical edge `f`, write `A(f)` for the subset of the already exposed
physical edges adjacent to `f` (sharing an endpoint with it).

## Adjacent `e_1,e_2`

Normalize `e_1=[1,2]` and `e_2=[1,3]`.  Distance 3 is the path `2-1-3`, and
there is no physical 3-edge.  The only distinct positive two-edge partition
of 4 is `1+3`, so distance 4 cannot be a nonedge path; hence `e_4` exists.

There are exactly four placement types for `e_4`:

| `A(e_4)` | canonical `e_4` | forced small paths | further physical edges | prefix spectrum / mex |
|---|---|---|---|---|
| empty | `[4,5]` | only `1+2=3` | `e_5` exists | `{1,2,3,4}` / 5 |
| `{e_1}` | `[2,4]` | `1+4=5`, `2+1+4=7` | `e_5,e_7` absent, `e_6` exists | `{1,2,3,4,5,7}` / 6 |
| `{e_2}` | `[3,4]` | `2+4=6`, `1+2+4=7` | `e_5` exists, `e_6,e_7` absent | `{1,2,3,4,6,7}` / 5 |
| `{e_1,e_2}` | `[1,4]` | `1+4=5`, `2+4=6` | `e_5,e_6` absent, `e_7` exists | `{1,2,3,4,5,6}` / 7 |

In the second row, `e_6` cannot be adjacent to `e_1`, since `1+6=7` would
collide with the exposed path `2+1+4=7`.  In the third row, `e_5` cannot be
adjacent to either `e_1` or `e_2`: the paths `1+5=6` and `2+5=7` would
respectively collide with `2+4=6` and `1+2+4=7`.

The second row also forces a cut restriction at order 18: deleting `e_1`
leaves the `e_2` endpoint branch on one side and the `e_4` endpoint branch on
the other, so both sides have at least two vertices.  Hence its smaller side
is at least 2 and `c_{e_1}>=2*16=32`.  Similarly, the third row has
`c_{e_2}>=32`.

## Disjoint `e_1,e_2`

Normalize `e_1=[1,2]` and `e_2=[3,4]`.  As proved above, `e_3` exists.  There
are exactly four placement types:

| `A(e_3)` | canonical `e_3` | forced small paths | further physical edges | prefix spectrum / mex |
|---|---|---|---|---|
| empty | `[5,6]` | none beyond the three edges | `e_4` exists | `{1,2,3}` / 4 |
| `{e_1}` | `[1,5]` | `1+3=4` | `e_4` absent, `e_5` exists | `{1,2,3,4}` / 5 |
| `{e_2}` | `[3,5]` | `2+3=5` | `e_4` exists, `e_5` absent | `{1,2,3,5}` / 4 |
| `{e_1,e_2}` | `[1,3]` | `1+3=4`, `3+2=5`, `1+3+2=6` | `e_4,e_5,e_6` absent, `e_7` exists | `{1,2,3,4,5,6}` / 7 |

In the third row, `e_4` cannot be adjacent to `e_1`, because `1+4=5` would
collide with `2+3=5`.  In the last row `e_3` joins the two disjoint exposed
edges.  Deleting it leaves at least the two endpoints of `e_1` on one side
and the two endpoints of `e_2` on the other.  At order 18 this gives
`s_{e_3}>=2` and `c_{e_3}>=32`.

## Exhaustiveness proof

An edge can meet each earlier edge in at most one endpoint.  If `e_1,e_2` are
disjoint, the adjacency set of `e_3` is therefore one of the four subsets of
`{e_1,e_2}`; meeting both makes `e_3` the bridge between them.  If `e_1,e_2`
are adjacent, an `e_4` meeting both must share their common endpoint: joining
their two outer endpoints would create a cycle.  This again gives exactly the
four table rows, up to endpoint relabeling.

For distance 5 the only distinct two-edge partitions are `1+4` and `2+3`;
for distance 6 they are `1+5` and `2+4`, together with the three-edge
partition `1+2+3`.  Testing adjacency and physical-edge existence in each row
gives every assertion in the tables.  If none of those paths exists, the
Leech requirement that the integer itself occur forces the corresponding
physical edge.  If one exists, uniqueness forbids a physical edge and also
forbids every second path with the same sum.  No other positive distinct-edge
composition is possible at these values.

Equivalently, each table's last column gives the complete spectrum internal
to the exposed forest.  Since all physical edges below the displayed exposed
maximum have already been decided, the forced-mex rule says that the next
physical edge has exactly the displayed mex.  This independently yields all
of the physical-edge existence assertions, including the forced `e_7` in the
two rows with spectrum `{1,2,3,4,5,6}`.

The disjoint matching checkpoint used by
`topology_distance_prefix_v8.py` is exactly the first row of the disjoint
table, not the other three rows.
