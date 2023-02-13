#ifndef IMPORT_SPEC_CONSTANTS
#define IMPORT_SPEC_CONSTANTS

//  #define SELECT_VIA_LOOP

/********
  *
  * Security game's parameters' valid ranges:
  *   - T <- Infinity
  *   - C <- Infinity
  *   - N <- [3,  16]
  *
  * Parameters (`t`, `c` `n`) defined as constants below:
  *
********/
#define T 11
#define C 11
#define N 4

#define BIT_ARRAY_WIDTH 4

/********
  *
  * Number of bits required to represent the number:
  *   - N - 1
  *
********/
#define BITS_N 2


/********
  *
  * The range of both Epoch and UserID values is extended by one to include a
  * "missing data" sentinel value name NEVER and NONE, respectively.
  * Furthermore, the number of array cells required to represent the protocol's
  * left balanced binary (LBBT) tree as a heap is equal to 2 ^ (BITS_N + 1) - 1.
  * We assign constants for the number of bits required to store a reference to
  * and Epoch, a UserID, or a vertex in the LBBT.
  *
  * Number of bits required to represent the number:
  *   - N
  *   - 2 * (2 ^ (BITS_N - 1))
  *
********/
#define BITS_USERID 3
#define BITS_VERTEX 3


/********
  *
  * The "missing data" sentinel values of NEVER and NONE, each indicate that a
  * reference to an Epoch or UserID, respectively, has no real contextual value.
  *
  * Constants defined as:
  *   - NEVER = (2 ^ BITS_T) - 1
  *   - NONE  = (2 ^ BITS_N) - 1
  *
********/
#define NONE  7


/********
  *
  * Definitions for constructing and indexing the heap representation of the LBBT.
  * The order of the tree is derived from the security parameter N and in turn
  * defines the size of the heap. Additionally, indexing offsets to the root node
  * and the first leaf node are specified.
  *
  * Observe the following example LBBT heap representation of for (N = 8):
  *
  *     Left-balanced Binary Tree Topology:
  *    
  *                +-----(14)-----+
  *               /                \
  *             (12)              (13)
  *            /    \            /    \
  *         (8)     (9)       (10)     (11)
  *        /   \   /   \     /    \   /    \
  *       0     1 2     3   4      5 6      7 
  *     
  *     Binary Heap Layout:
  *     
  *       Index:   0   1   2   3   4   5   6   7   8   9  10  11  12  13  14
  *       Array: [  ][  ][  ][  ][  ][  ][  ][  ][  ][  ][  ][  ][  ][  ][  ]
  *       Nodes:  14  12  13   8   9  10  11   0   1   2   3   4   5   6   7
  *
  * Constants defined as:
  *   - TREE_ORDER = 2 ^ (BITS_N + 1) - 1
  *   - ROOT       = 0
  *   - LEAF       = TREE_ORDER / 2
  *
********/
#define TREE_ORDER 7
#define ROOT       0
#define LEAF       3


/********
  *
  * The model must often iterate over the entire domain of valid (non-missing)
  * Epochs, UserIDs, Vertices, or post-order tree levels. To facilate these
  * traversals, constants are defined indicating the upper and lower bounds of
  * the contiguous, discrete domains.
  *
  * Constants defined as:
  *   - FINAL_USERID = ( N - 1 )
  *   - FINAL_VERTEX = ( TREE_ORDER  - 1 )
  *   - ROOT_LEVEL   = ( BITS_VERTEX - 1 )
  *
********/
#define FIRST_USERID 0
#define FINAL_USERID 3

#define FIRST_VERTEX 0
#define FINAL_VERTEX 6

#define LEAF_LEVEL 0
#define ROOT_LEVEL 2

#endif /* IMPORT_SPEC_CONSTANTS */
