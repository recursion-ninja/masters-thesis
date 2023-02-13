# TreeKEM Model Changelog

## Benchmarked `pan` compilation directives

**Consideration directive set:**

  - COLLAPSE
  - HC
  - MA
  - SPACE
  - VECTORS

**Verification performance:**

*Best space/time usage, biases towards space*

| N | T |    MiB⁑   |  sec⁑ | Best Directive Set |
|:-:|:-:|----------:|------:|:-------------------|
| 4 | 4 | 10253.608 | 59300 | MA=59, SPACE       |
| 4 | 5 | | | |
| 5 | 4 | | | |
| 5 | 5 | | | |


## Created `PopCount` CPP macro

  - Counts number of set bits

  - Used Spin to verify correctness for:
      * Each bit width `w in [ 1, 16 ]`...
      * All `v` values in [ 0, 2^w - 1 ]`...
      * `PopCount(v)` equaled the loop and individual bit count equivelent

  - Used `PopCount` instead of loops to count bits throughout model


## Created general nondeterministic selection function

  - Pass bit array with each set bit index representing a valid member ID choice.

  - Use `PopCount` to count selection possibilities

  - Nondeterministically select value in range `[ 0, PopCount(buffer) - 1 ]`

  - Loop to selected bit and return index, (selected member ID)


## Removed extraneous global state variables

  - The following were no longer needed:
      * `byte attendees`
      * `byte absentees`
      * `byte unsafeIDs`
      * `bool nonCommitment`


## Refactored to be "history-less"

  - Changed representation of hoarding group members from byte array to "bit-array:"
      * `byte hoarding[N]` --> `unsigned hoardPrior : N`

  - Global variable `hoardPrior` tracks which member IDs have hoarded secrets from a *previous* epoch.

  - CGKG game loop has local `unsigned hoardNewly : N` to tracking which member IDs have started hoarding secrets in the *current* epoch.



## Move `groupMost` to `State-Global.pml`

  - Renamed `groupMost` to `highestID`, more descriptive.


## Created module: "Enumeration.pml"

  - Added `inline` definitions for populating a "bit-array" with valid member IDs for:
      * Corruption
      * Hoarding
      * Invitee (member to be added to group)


## Removed `State-Networking.pml`

  - Functionality was moved into modules:
      * `CGKA-Security-Game.pml`
      * `Enumeration.pml`
      * `State-Global.pml`


# Results:

## State-vector reduction

  - Old: `96`

  - New: `68`
