#ifndef IMPORT_SPEC_GLOBALS
#define IMPORT_SPEC_GLOBALS


/********
  *
  * Advantage:
  *
  * In the following, a (`t`, `c`, `n`)-attacker is an attacker `A` that runs in time at most `t`,
  * makes at most `c` challenge queries, and never produces a group with more than `n` members.
  * The attacker wins the CGKA security game if they correctly guesses the random bit `b` in
  * the end and the safety predicate `P` evaluates to true on the queries made by the attacker.
  *
  * Parameters (`t`, `c`, `n`), are defined via pre-preocessor constants as the macro symbols
  * `T`, `C`, and `N`, along with derivative constants, in the following "#included" Promela file:
  *
********/

#include "Parameterized-Constants.pml"


/****
  *
  * Global state of the CGKA security game.
  *
****/

local unsigned challenge : T; // Has the attacker challenged in an epoch?
//local bool  challenge[T]; // Has the attacker challenged in an epoch?
local byte leadership[T]; // Which member initiated the epoch?
local bool learnedKey[T]; // Attacker knows the group key of current epoch?

local bool membership[N]; // Group membership of current epoch
local byte   hoarding[N]; // Epoch from which the user saves secrets

local bool     unsafe[N];               // Members which require a change to update
local unsigned unsafeIDs : BITS_USERID; // Flags set within unsafe

local unsigned epoch     : BITS_EPOCH;  // The current epoch

local unsigned originID  : BITS_USERID; // ID of the  member
local unsigned targetID  : BITS_USERID; // ID of the effected member


#endif /* IMPORT_SPEC_GLOBALS */
