#include "Parameterized-Constants.pml"
#include "State-Global.pml"
#include "State-Networking.pml"


/********
    *
    * Important LTL Properties:
    *
    *   - Totality
    *   - FSU (Future Secrecy with Updates)
    *   - PCS (Post-Compromise Security)
    *
********/


/****
  *
  * LTL: Totality
  *
  * The CGKA game always halts
  *
****/
/**
ltl Totality
{
  <> CGKA@end_of_game
}
**/


/****
  *
  * LTL: FSU (Future Secrecy with Updates)
  *
****/
/**
#define never_trivially_hoard_then_corrupt \
( []( CGKA@move_corrupt -> hoarding[targetID] == NEVER ) )


#define future_secrecy_of_epoch( t ) \
(  \
    (  \
        <> \
        (  \
            ( CGKA@start_of_epoch ) \
        && \
            ( epoch == (t + 1) ) \
        && \
            ( !(learnedKey[t]) ) \
        )  \
    ) \
-> \
    (  \
        ( !(learnedKey[t]) ) \
    U  \
        ( CGKA@end_of_game ) \
    )  \
)


ltl FSU
{ 
    never_trivially_hoard_then_corrupt ->
    (   future_secrecy_of_epoch( 0 )
    &&  future_secrecy_of_epoch( 1 )
    &&  future_secrecy_of_epoch( 2 )
    )
}
**/


/****
  *
  * LTL: PCS (Post-Compromise Security)
  *
****/
/**/
ltl PCS
{ 
    [] ( ( CGKA@start_of_epoch && ( unsafeIDs == 0 ) ) -> ( !( learnedKey[epoch] ) ) )
}
/**/
/*
#define corrupt_then_recover( id ) \
(  \
   ( \
      ( CGKA@move_corrupt ) \
   && \
      ( targetID == id    ) \
   ) \
-> \
    (  \
        <> \
        ( \
            (  \
                ( CGKA@move_remove ) \
            && \
                ( targetID == id ) \
            )  \
        || \
            (  \
                ( CGKA@move_update ) \
            && \
                ( originID == id ) \
            )  \
        ) \
    ) \
)


ltl PCS
{ 
    (
        []
        (  corrupt_then_recover ( 0 )
        && corrupt_then_recover ( 1 )
        && corrupt_then_recover ( 2 )
        && corrupt_then_recover ( 3 )
        )
        && CGKA@end_of_game
    )
    ->
    ( !(learnedKey[FINAL_EPOCH]) )
}


#define post_compromise_security_of_epoch( id ) \
(  \
    [] \
    (  \
        (   CGKA@start_of_epoch \
        && ( targetID == id ) \
        ) \
    -> \
        ( attackerKnowledge[epoch].node[ROOT] != NodeIsKnown ) \
    )  \
)

*/











/*
ltl attendees_more_than_one
{
  [](attendees > 1)
}


ltl attendees_absentees_sum
{
  []( { attendees + absentees == N } )
}
*/