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

local unsigned epoch     : BITS_EPOCH;  // The current epoch
local unsigned unsafeIDs : BITS_USERID; // Number of unsafeIDs

local bool  challenge[T]; // Has the attacker challenged in an epoch?
local bool membership[N]; // Group membership of current epoch
local bool     unsafe[N]; // Members which require a change to update
local byte   hoarding[N]; // Epoch from which the user saves secrets


/****
  *
  * The attacker's knowledge of the agreed upon group key for each epoch.
  *
  *   - Undefined: The group key will be created in a future epoch. Currently,
  *                the key does not exist, and hence is undefined and unknowable.
  *
  *   - Unknown:   The group key was created in the *current* epoch and currently
  *                the attacker has yet to learn the key.
  *
  *   - Revealed:  The attacker learned the group key by using the either the
  *                'Corrupt' or 'Reveal' Oracle(s) in the epoch (past or present).
  *
  *   - Secret:    The group key was created in a past epoch and the attacker
  *                does not know the key.
  *
  *   - Gleaned:   The attacker learned the group key *without* directly using
  *                an oracle.
  *
  *         (1)   Gleaned    (5)
  *            ⬈          ⬉
  *  Undefined               Secret
  *            ⬊          ⬈
  *         (2)   Unknown    (4)
  *              (3) ⬇
  *               Revealed 
  *
  *  Transitions:
  *
  *    1. A new epoch advanced
  *    2. 
  *    3. 
  *    4. 
  *    5. 
  *
****/
mtype:KeyState = { Undefined, Unknown, Revealed, Secret, Gleaned };

local mtype:KeyState groupKey[T];


#endif /* IMPORT_SPEC_GLOBALS */
