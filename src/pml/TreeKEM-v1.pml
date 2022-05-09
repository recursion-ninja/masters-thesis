#ifndef IMPORT_SPEC_ATTACKER
#define IMPORT_SPEC_ATTACKER


#include "Parameterized-Constants.pml"
#include "State-Global.pml"


/****
  *
  * Attacker's protocol specific knowledgebase.
  *
  * +=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=+
  * |                                   |
  * |  PROTOCOL: TreeKEM Version 1.0.0  |
  * |                                   |
  * +=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=+
  *
****/


/****
  *
  * Any TreeKEM "module" version must export the following "inline" defininitions:
  *
  * Exports:
  *   - attacker_amend_knowledge
  *   - attacker_check_knowledge
  *   - attacker_initialize
  *   - attacker_learn_root
  *   - attacker_learn_leaf
  *   - attacker_study_message
  *   - print_attacker_knowledge
  *
  * The exported definitions correspond to how the attacker observes, stores,
  * and updates knowledge about the TreeKEM protocol's LBBT of secret keys.
  * The goal of the attacker is to know the value of the shared secret symetric
  * key stored at the root node.
  *
  * The definitions are used by the:
  *   - CGKA security game control flow
  *   - CGKA Oracles
  *
****/


/****
  *
  * The attacker knowledgebase keeps track of which verticies within the
  * TreeKEM (version 1) LBBT for with the attacker knows the associated secret key.
  * Each node in the LBBT can be in one of *five* mutually exclusive states.
  *
  * Vertex states:
  *   - Uninhabited: This node does not exist  and there exists 0 leaves in the subtree
  *   - MockUnknown: This node does not exist  and there exists 1 leaf   in the subtree
  *   - MockIsKnown: This node does not exist  and there exists 1 leaf   in the subtree
  *   - NodeUnknown: This node          exists and there exists 1 or more leaves in the subtree
  *   - NodeIsKnown: This node          exists and there exists 1 or more leaves in the subtree
****/
mtype:VertexInfo = { Uninhabited, MockUnknown, MockIsKnown, NodeUnknown, NodeIsKnown };


/****
  *
  * The attacker knowledgebase represents the TreeKEM (version 1) LBBT as a heap.
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
  *
  * Similarly for (N = 4):
  *
  *     Left-balanced Binary Tree Topology:
  *    
  *             (6)
  *            /    \
  *         (4)     (5)
  *        /   \   /   \
  *       0     1 2     3
  *     
  *     Binary Heap Layout:
  *     
  *       Index:   0   1   2   3   4   5   6
  *       Array: [  ][  ][  ][  ][  ][  ][  ]
  *       Nodes:   6   4   5   0   1   2   3
  *
  *
****/
typedef TreeKeys { mtype:VertexInfo node[ TREE_ORDER ]  };


/****
  *
  * The attacker knowledgebase must track knowledge over time, as information
  * from a past epoch could be learned and effect the attacker's knowledge of
  * subsequent epochs. Consequently the attacker knowledgebase is represented
  * as an array of heaps.
  *
****/
TreeKeys attackerKnowledge[T];


/****
  *
  * Export inline definitions for:
  *   - attacker_amend_knowledge
  *   - attacker_check_knowledge
  *   - attacker_initialize
  *   - attacker_learn_root
  *   - attacker_learn_leaf
  *   - attacker_study_message
  *   - print_attacker_knowledge
  *
****/


inline attacker_amend_knowledge ( named_epoch )
{
    // TODO:
    // Starting from 'named_epoch' the attacker updates knowledge.
    // Assumes that some knowledge within 'named_epoch' has changed.
    if
    :: named_epoch >= epoch -> skip
    :: else -> atomic
        {
            unsigned t : BITS_EPOCH;
            for ( t : named_epoch + 1 .. epoch )
            {
                attacker_copy_epoch_knowledge ( t - 1 );
                attacker_updates_knowledge    ( t     );
            }
            attacker_check_knowledge ( epoch );
        }
    fi
}


inline attacker_check_knowledge ( named_epoch )
{
    d_step
    {
        unsigned e : BITS_EPOCH;
        for ( e : FIRST_EPOCH .. named_epoch )
        {
            learnedKey[named_epoch] = attackerKnowledge[e].node[ROOT] == NodeIsKnown;
        }
    }
}


inline attacker_initialize ( )
{
    d_step
    {
        unsigned t : BITS_EPOCH;
        for ( t : FIRST_EPOCH .. FINAL_EPOCH )
        {
            d_step
            {
                unsigned v : BITS_VERTEX;
                for ( v : FIRST_VERTEX .. FINAL_VERTEX )
                {
                    attackerKnowledge[t].node[v] = Uninhabited
                }
            }
            learnedKey[t] = false;
        }
    }
}


inline attacker_learn_root ( named_epoch )
{
    attackerKnowledge[named_epoch].node[ROOT] -> NodeIsKnown;
    learnedKey[named_epoch] = true;
}


inline attacker_learn_leaf ( named_epoch, memberID )
{
    // Attacker learns the node information
    attackerKnowledge[named_epoch].node[LEAF + memberID] -> NodeIsKnown;
    d_step
    {
        unsigned height : BITS_VERTEX;
        unsigned offset : BITS_VERTEX = LEAF;
        unsigned spine  : BITS_VERTEX = LEAF + memberID;
        for ( height : 0 .. BITS_VERTEX - 1 )
        {
            d_step
            {
                if
                :: attackerKnowledge[named_epoch].node[spine] == NodeUnknown -> attackerKnowledge[named_epoch].node[spine] = NodeIsKnown
                :: attackerKnowledge[named_epoch].node[spine] == MockUnknown -> attackerKnowledge[named_epoch].node[spine] = MockIsKnown
                :: else
                fi
                spine = (spine - 1) / 2;
            }
        }
    }
}


inline attacker_study_message ( e, inviter, subject )
{
    atomic
    {
        // If the attacker has know knowledge of the epoch,
        // meaning that all cell values are "Uninhabited,"
        // then it is the first time we have entered the epoch
        // and the cell values should be initialized as either:
        //   * NodeUnknown
        //   * MockUnknown
        //   * Uninhabited
        bool noEpochKnowledge;
        attacker_has_no_epoch_knowledge ( e );
        if
        :: noEpochKnowledge -> attacker_init_epoch_knowledge ( e );
        :: else
        fi
        
        //       referenceEpoch = (e == 0) ? e : e - 1;
        unsigned referenceEpoch : BITS_EPOCH = e ;
        if
        :: e != 0 -> referenceEpoch--;
        :: else
        fi

        attacker_copy_epoch_knowledge ( referenceEpoch );
        attacker_updates_knowledge    ( e );
        attacker_check_knowledge      ( e );
    }
}


inline print_attacker_knowledge ( )
{
    d_step
    {
        printf ( "\n\tAttacker Knowledge:" );
        unsigned pt : BITS_EPOCH;
        for ( pt : FIRST_EPOCH .. FINAL_EPOCH )
        {
            printf ( "\n\t  >>>\t@ %d\t<<<", pt );
            d_step
            {
                printf ( "\n\t  ---\t-----\t---" );
                unsigned d : BITS_VERTEX = 2;
                unsigned v : BITS_VERTEX;
                for ( v : FIRST_VERTEX .. FINAL_VERTEX )
                {
                    if
                    :: ( v + 1 ) == d ->
                        printf ( "\n\t  ---\t-----\t---" );
                        if
                        :: d < N -> d = d * 2;
                        :: else
                        fi
                    :: else
                    fi

                    if
                    :: attackerKnowledge[pt].node[v] == MockUnknown -> printf ( "\n\t  %d [\tx\t]", v )
                    :: attackerKnowledge[pt].node[v] == NodeUnknown -> printf ( "\n\t  %d [\tX\t]", v )
                    :: attackerKnowledge[pt].node[v] == MockIsKnown -> printf ( "\n\t  %d [\to\t]", v )
                    :: attackerKnowledge[pt].node[v] == NodeIsKnown -> printf ( "\n\t  %d [\tO\t]", v )
                    :: attackerKnowledge[pt].node[v] == Uninhabited -> printf ( "\n\t  %d [\t \t]", v)
                    :: else                                         -> printf ( "\n\t  %d [\t?\t]", v )
                    fi
                }
            printf ( "\n\t  ---\t-----\t---" );
            printf ( "\n" );
            }
        };
        printf ( "\n" );
    }
}


/****
  *
  * Supporting inline definitions:
  *   - attacker_copy_epoch_knowledge
  *   - attacker_has_no_epoch_knowledge
  *   - attacker_init_epoch_knowledge
  *   - attacker_updates_knowledge
  *   - attacker_wipe_inviter_knowledge
  *   - existance_of_subtree
  *   - knowledge_of_subtree
  *
****/


inline attacker_has_no_epoch_knowledge ( e )
{
    d_step
    {
        bool allUninhabited = true;
        unsigned v : BITS_VERTEX;
        for ( v : FIRST_VERTEX .. FINAL_VERTEX )
        {
            allUninhabited = allUninhabited && (attackerKnowledge[e].node[v] == Uninhabited)
        }
        noEpochKnowledge = allUninhabited;
    }
}


inline attacker_init_epoch_knowledge ( e )
{   atomic {

    unsigned height  : BITS_VERTEX;
    unsigned offset  : BITS_VERTEX = LEAF;
    unsigned width   : BITS_VERTEX = (TREE_ORDER / 2) + 1;
    unsigned treetop : BITS_VERTEX = BITS_VERTEX - 1;    
    for ( height : 0 .. treetop )
    {
        d_step
        {
            unsigned n : BITS_VERTEX;
            for ( n : 0 .. width - 1 )
            {
                d_step
                {
                    unsigned v : BITS_VERTEX = offset + n;
                    mtype:VertexInfo info = Uninhabited;
                    if
                    // Root node case(s)
                    :: height == treetop -> info = NodeUnknown
                    // Leaf node case(s)
                    :: height == 0 ->
                        if
                        // No knowledge from excluded group members
                        :: n >= N || !(membership[n]) -> info = Uninhabited
                        :: else                       -> info = NodeUnknown
                        fi
                    // Internal node case(s)
                    :: else ->
                        bool voidL, voidR;
                        d_step
                        {
                            unsigned childL : BITS_VERTEX = v * 2 + 1;
                            unsigned childR : BITS_VERTEX = v * 2 + 2;
                            // Check current epoch for existance of subtrees
                            bool existanceOfSubtree;
                            existance_of_subtree ( e, childL);
                            voidL = !existanceOfSubtree;
                            existance_of_subtree ( e, childR);
                            voidR = !existanceOfSubtree;
                        }
                        if
                        ::  voidL &&  voidR -> info = Uninhabited
                        :: !voidL &&  voidR -> info = MockUnknown
                        ::  voidL && !voidR -> info = MockUnknown
                        :: !voidL && !voidR -> info = NodeUnknown
                        fi
                    fi
                    attackerKnowledge[e].node[v] = info;
                }
            };
            offset = offset / 2;
            width  = width  / 2;
        }
    }
}   }


inline attacker_copy_epoch_knowledge( e )
{   atomic {

    unsigned height : BITS_VERTEX;
    unsigned offset : BITS_VERTEX = LEAF;
    unsigned spine  : BITS_VERTEX = LEAF + leadership[e];
    unsigned width  : BITS_VERTEX = (TREE_ORDER / 2) + 1;
    for ( height : 0 .. BITS_VERTEX - 1 )
    {
        d_step
        {
            unsigned n : BITS_VERTEX;
            for ( n : 0 .. width - 1 )
            {
                unsigned v : BITS_VERTEX = offset + n;
                bool knowledgeOfSubtree;
                knowledge_of_subtree ( e, v );
                if
                :: v == spine -> skip
                :: v != spine ->
                    if
                    :: attackerKnowledge[e+1].node[v] == NodeUnknown && knowledgeOfSubtree -> attackerKnowledge[e+1].node[v] = NodeIsKnown
                    :: attackerKnowledge[e+1].node[v] == MockUnknown && knowledgeOfSubtree -> attackerKnowledge[e+1].node[v] = MockIsKnown
                    :: else
                    fi
                fi
            };
            offset = offset      / 2;
            spine  = (spine - 1) / 2;
            width  = width       / 2;
        }
    }
    print_attacker_knowledge ( );
}   }


inline attacker_updates_knowledge ( e )
{   atomic {

    unsigned height  : BITS_VERTEX;
    unsigned offset  : BITS_VERTEX = LEAF;
    unsigned width   : BITS_VERTEX = (TREE_ORDER / 2) + 1;
    unsigned treetop : BITS_VERTEX = BITS_VERTEX - 1;    
    for ( height : 0 .. treetop )
    {
        d_step
        {
            unsigned n : BITS_VERTEX;
            for ( n : 0 .. width - 1 )
            {
                unsigned v : BITS_VERTEX = offset + n;
                if
                :: height == 0 -> skip // Leaf node case
                :: else ->
                    bool knowsL, knowsR, voidL, voidR;
                    atomic
                    {
                        unsigned childL : BITS_VERTEX = v * 2 + 1;
                        unsigned childR : BITS_VERTEX = v * 2 + 2;

                        // Check current epoch for existance of subtrees
                        bool existanceOfSubtree;
                        existance_of_subtree ( e, childL);
                        voidL = !existanceOfSubtree;
                        existance_of_subtree ( e, childR);
                        voidR = !existanceOfSubtree;
                        
                        // Check previous epoch for knowledge of subtrees
                        bool knowledgeOfSubtree;
                        knowledge_of_subtree ( e, childL);
                        knowsL = knowledgeOfSubtree;
                        knowledge_of_subtree ( e, childR);
                        knowsR = knowledgeOfSubtree;
                    }
                    if
                    // Root node case(s)
                    :: height == treetop ->
                        if 
                        :: knowsL || knowsR -> attackerKnowledge[e].node[v] = NodeIsKnown
                        :: else             -> attackerKnowledge[e].node[v] = NodeUnknown
                        fi
                    // Internal node case(s)
                    :: else ->
                        if
                        ::  voidL &&  voidR                       -> attackerKnowledge[e].node[v] = Uninhabited
                        :: !voidL &&  voidR &&             knowsR -> attackerKnowledge[e].node[v] = MockIsKnown
                        :: !voidL &&  voidR &&            !knowsR -> attackerKnowledge[e].node[v] = MockUnknown
                        ::  voidL && !voidR &&  knowsL            -> attackerKnowledge[e].node[v] = MockIsKnown
                        ::  voidL && !voidR && !knowsL            -> attackerKnowledge[e].node[v] = MockUnknown
                        :: !voidL && !voidR &&  knowsL &&  knowsR -> attackerKnowledge[e].node[v] = NodeIsKnown
                        :: !voidL && !voidR && !knowsL &&  knowsR -> attackerKnowledge[e].node[v] = NodeIsKnown
                        :: !voidL && !voidR &&  knowsL && !knowsR -> attackerKnowledge[e].node[v] = NodeIsKnown
                        :: !voidL && !voidR && !knowsL && !knowsR -> attackerKnowledge[e].node[v] = NodeUnknown
                        fi
                    fi
                fi
            };
            offset = offset / 2;
            width  = width  / 2;
        }
    }
}   }


inline existance_of_subtree ( t, v )
{
    existanceOfSubtree = attackerKnowledge[t].node[v] != Uninhabited
}


inline knowledge_of_subtree ( t, v )
{
    knowledgeOfSubtree = attackerKnowledge[t].node[v] == NodeIsKnown || attackerKnowledge[t].node[v] == MockIsKnown
}


#endif /* IMPORT_SPEC_ATTACKER */ 