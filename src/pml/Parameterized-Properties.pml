#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"


ltl game_totality
{ 
  <>concludedCGKA
}


/*
ltl trivial_safety
{ 
  []( attackerKnowledge[epoch].node[ROOT] == NodeIsKnown -> ( triviality && epoch <= FINAL_EPOCH ) )
}


ltl challenge
{
  []( { concludedCGKA && !(triviality) } -> { attackerKnowledge[FINAL_EPOCH].node[ROOT] != NodeIsKnown } )
}


ltl attendees_more_than_one
{
  [](attendees > 1)
}


ltl attendees_absentees_sum
{
  []( { attendees + absentees == N } )
}
*/