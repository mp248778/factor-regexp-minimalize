! Copyright (C) 2009 Daniel Ehrenberg, Michal Pachucki.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel sequences regexp.transition-tables fry assocs accessors arrays hashtables
regexp.dfa regexp.classes lists prettyprint vectors locals sets combinators 
deques math classes.tuple sorting ;

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
    2array [ elems>> length 0 = not ] filter sequence>cons
    ; 

! working should be per letter, not per alphabet (so it would be faster) 


! minimization

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



! reconstruct transition table


: number-partitions ( partitions -- partitions' )
    [ elems>> natural-sort ] lmap [ dup first '[ _ 2array ] map ] lmap list>array concat ;

: has-conditions? ( assoc -- ? )
    values [ condition? ] any? ;

: canonical-state? ( state transitions state-classes -- ? )
    '[ dup _ at =  ] swap '[ _ at has-conditions? ] bi or ;

: delete-duplicates ( transitions state-classes -- new-transitions )
    dupd '[ drop _ _ canonical-state? ] assoc-filter ;

: combine-states ( table classes -- smaller-table )
    [ transitions-at ] keep
    '[ _ delete-duplicates ] change-transitions ;

: combine-state-transitions ( hash -- hash )
    H{ } clone tuck '[
        _ [ 2array <or-class> ] change-at
    ] assoc-each [ swap ] assoc-map ;

: combine-transitions ( table -- table )
    [ [ combine-state-transitions ] assoc-map ] change-transitions ;


! set proper numbering


: table>state-numbers ( table -- assoc )
    transitions>> keys <enum> [ swap ] H{ } assoc-map-as ;

: number-states ( table -- newtable )
    dup table>state-numbers transitions-at ;


! minimize

: my-minimize ( table -- new-table )
    number-states
    dup prepare-state-partitioning
    (my-minimize) number-partitions >hashtable
    combine-states
    combine-transitions
    expand-ors ;
