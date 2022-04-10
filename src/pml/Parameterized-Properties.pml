#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"

ltl challenge
{
  []( (concludedCGKA && !triviality) -> attackerKnowledge[epoch].node[ROOT] != NodeIsKnown)
}


/*
ltl trivial_safety
{ 
  []( (triviality && epoch <= FINAL_EPOCH) -> attackerKnowledge[epoch].node[ROOT] != NodeIsKnown)
}


ltl game_totality
{ 
  <>concludedCGKA
}


ltl attendees_more_than_one
{
  [](attendees > 1)
}


ltl attendees_absentees_sum
{
  [](attendees + absentees == N)
}
*/