#ifndef IMPORT_SPEC_GLOBALSTATE
#define IMPORT_SPEC_GLOBALSTATE


/********
  *
  * Advantage:
  *
  * In the following, a (`t`, `c`, `n`)-attacker is an attacker `A` that runs in time at most `t`,
  * makes at most `c` challenge queries, and never produces a group with more than `n` members.
  * The attacker wins the CGKA security game if they correctly guesses the random bit `b` in
  * the end and the safety predicate `P` evaluates to true on the queries made by the attacker.
  *
********/

#include "parameterized-constants.pml"


/****
  *
  * Global state of the CGKA security game.
  *
****/

local unsigned epoch     : BITS_EPOCH;  // The current epoch
local unsigned unsafeIDs : BITS_USERID; // Number of unsafeIDs

local bool  challenge[T]; // Has the attacker challenged in an epoch?
local bool membership[N]; // Group membership of current epoch
local bool     unsafe[N]; // Members which require a change to update
local byte   hoarding[N]; // Epoch from which the user saves secrets

#endif /* IMPORT_SPEC_GLOBALSTATE */
