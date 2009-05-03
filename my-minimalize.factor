! Copyright (C) 2009 Michal Pachucki.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel sequences regexp.transition-tables fry assocs accessors arrays hashtables
regexp.dfa regexp.classes lists prettyprint vectors locals sets combinators 
deques math classes.tuple 

tools.continuations
;

IN: my-minimalize
TUPLE: subset working elems ;

C: <subset> subset

:: (reverse-transition-table) ( dict letter key' key -- )
    key' condition? 
        [ 
            key' condition-states 
            [ 
                H{ { key key } } swap associate
                f dict at
                dict set-at
                f dict [ 1 - ] change-at
            ] each 
        ] 
        [ H{ { key key } } key key' letter dict [ drop H{ } clone ] cache [ drop H{ } clone ] cache set-at ] if ;

: reverse-transition-table ( transition-table -- reversed-transition-table ) 
    transitions>> unzip [ unzip rot [ [ (reverse-transition-table) ] 3curry ] curry 2map ] { } 2map-as concat 
    H{ { f -1 } } clone dup '[ _ swap call( dict -- ) ] swapd each 
    f over delete-at ; 

: prepare-state-partitioning ( table -- rev-trans-table partitions )
    {
        [ reverse-transition-table values sequence>cons ]
        [ [ transitions>> keys ] [ final-states>> keys ] bi diff t swap <subset> ]
        [ final-states>> keys t swap <subset> ]
    } cleave
    2list ! choose smaller one
    ; 

! working should be per letter, not per alphabet (so it would be faster) 

: create-sets ( first-working? set1 set2 -- set1' set2' )
    [ f swap <subset> ] bi@ rot 
        [ [ t >>working ] bi@ ] 
        [ 2dup [ elems>> length ] bi@ < [ swap ] when t >>working ] 
    if ;
    
: (sub-partition) ( partition set -- new-partitions )
    [ tuple-slots first2 ] dip '[ _ key? ] partition
    2dup [ empty? ] either?
    [ dup empty? [ swap ] unless drop <subset> 1list ] [ create-sets 2list ] if ;


: sub-partition ( partitions set -- new-partitions )
    +nil+ swap '[ _ (sub-partition) swap lappend ] foldr ;


: lfind ( list q -- elem )
    over +nil+? [ 2drop f ]
    [ 
        2dup [ car>> ] [ call( obj -- t/f ) ] bi*
        [ drop car>> ] [ [ cdr>> ] dip lfind ] if
    ] if ;

: find-next-set ( partitions -- set )
    [ working>> ] lfind ;

: ingoing-states ( states rev-trans-table-elt -- states ) 
    '[ _ at assoc-union ] H{ } swap reduce ;

: (my-minimize) ( rev-trans-table partitions -- new-partitions )
    [ dup ] bi@ find-next-set dup f = [ drop 2nip ] 
    [ 
        f >>working elems>> 
        '[ _ swap ingoing-states sub-partition ] foldr
        (my-minimize)
    ] if ; recursive

: reverse-partitions ( partitions -- hashtable )
    [ [ id>> ] [ elems>> swap '[ _ 2array ] map ] bi ] map concat
    >hashtable ;

: update-destinations ( table partitions -- )
    [ dup transitions>> ] [ reverse-partitions ] bi*
    '[ [ _ at ] assoc-map ] assoc-map
    >>transitions drop ;

: update-transitions ( table partitions -- )
    2dup update-destinations
    over transitions>> '[ [ id>> ] [ elems>> [ _ at ] map assoc-combine 2array ] bi ] map >hashtable 
    >>transitions drop
    ;

: update-border-states ( table partitions -- )
    [ 
        over start-state>> '[ elems>> [ _ = ] find nip ] find 
        nip id>> >>start-state drop
    ] 
    [
        over final-states>> keys '[ dup elems>> _ intersect empty? [ drop { } ] [ id>> 1array ] if ] map concat 
        dup zip >hashtable >>final-states drop
    ] 
    2bi ;

: table>state-numbers ( table -- assoc )
    transitions>> keys <enum> [ swap ] H{ } assoc-map-as ;

: number-states ( table -- newtable )
    dup table>state-numbers transitions-at ;

: my-minimize ( table -- new-table )
    number-states
    dup prepare-state-partitioning
    break
    (my-minimize) list>array [ elems>> empty? not ] filter
    dupd [ update-transitions ] [ update-border-states ] 2bi ;
