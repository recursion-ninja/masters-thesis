#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"

#define future_secrecy_of_epoch( t ) \
(  \
    (   <> \
        (  \
            ( CGKA@start_of_epoch ) \
        && \
            ( epoch == (t + 1)) \
        && \
            ( attackerKnowledge[t].node[ROOT] != NodeIsKnown ) \
        )  \
    ) \
-> \
    (  \
        ( attackerKnowledge[t].node[ROOT] != NodeIsKnown ) \
    U  \
        ( CGKA@end_of_game ) \
    )  \
)


#define trivial_hoard_then_corrupt( id ) \
(  \
    (  \
        ( CGKA@move_hoard ) \
    && \
        ( activeID == id  ) \
    )  \
-> \
    (   <> \
        (  \
           ( CGKA@move_corrupt ) \
        && \
           ( activeID == id    ) \
        )  \
    )  \
)


#define no_trivial_hoard_then_corrupt( id ) \
( \
    (  \
        ( CGKA@move_hoard ) \
    && \
        ( activeID == id  ) \
    ) \
-> \
    ( \
        (  \
            !( CGKA@move_corrupt ) \
        && \
             ( activeID == id    ) \
        )  \
    U  \
        ( CGKA@end_of_game ) \
    ) \
)


/*
( ( t < epoch && attackerKnowledge[t].node[ROOT] != NodeIsKnown) -> ( ( attackerKnowledge[t].node[ROOT] != NodeIsKnown ) U concludedCGKA ) )
*/


ltl future_secrecy
{ 
    ( [] (    no_trivial_hoard_then_corrupt( 0 )
          &&  no_trivial_hoard_then_corrupt( 1 )
          &&  no_trivial_hoard_then_corrupt( 2 )
          &&  no_trivial_hoard_then_corrupt( 3 )
         )
    )
    ->
    (   future_secrecy_of_epoch( 0 )
    &&  future_secrecy_of_epoch( 1 )
    &&  future_secrecy_of_epoch( 2 )
    )
}


/*
ltl game_totality
{ 
  <> ( CGKA@end_of_game )
}
*/

/*
ltl future_secrecy
{ 
    []
    (   (   ( CGKA@start_of_epoch && epoch == 1 && attackerKnowledge[0].node[ROOT] != NodeIsKnown)
        ->  ( ( attackerKnowledge[0].node[ROOT] != NodeIsKnown ) U CGKA@end_of_game )
        )
    &&  (  ( 1 < epoch && attackerKnowledge[1].node[ROOT] != NodeIsKnown) -> ( ( attackerKnowledge[1].node[ROOT] != NodeIsKnown ) U concludedCGKA ) )
    &&  (  ( 2 < epoch && attackerKnowledge[2].node[ROOT] != NodeIsKnown) -> ( ( attackerKnowledge[2].node[ROOT] != NodeIsKnown ) U concludedCGKA ) )
    )
}


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