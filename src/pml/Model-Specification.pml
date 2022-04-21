#include "CGKA-Security-Game.pml"
#include "Parameterized-Constants.pml"
#include "Parameterized-Properties.pml"
#include "State-Global.pml"
#include "State-Networking.pml"

init
{
    CGKA_initialize    ( );
    CGKA_create_group  ( );
    CGKA_security_game ( );
}
