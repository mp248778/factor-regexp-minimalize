! Copyright (C) 2009 Michal Pachucki.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel sequences regexp.transition-tables fry assocs accessors arrays hashtables
regexp.dfa regexp.classes lists prettyprint vectors locals sets combinators 
deques math classes.tuple


io vocabs.loader regexp.parser regexp.nfa regexp.disambiguate regexp.minimize
tools.walker
;

IN: my-minimalize
TUPLE: subset elems id ;
TUPLE: partitions sets ;
TUPLE: working-set sets-vector sets-ids ;
TUPLE: minimize-state partitions working-set ;

C: <subset> subset
C: <working-set> working-set
C: <partitions> partitions
C: <minimize-state> minimize-state

:: (reverse-transtion-table) ( dict letter key' key -- )
    key key key' letter dict [ drop H{ } clone ] cache [ drop H{ } clone ] cache set-at ;

: reverse-transtion-table ( transition-table -- reversed-transition-table ) 
    transitions>> unzip [ unzip rot [ [ (reverse-transtion-table) ] 3curry ] curry 2map ] { } 2map-as concat 
    H{ } clone dup '[ _ swap call( dict -- ) ] swapd each 
    ; 

: prepare-state-partitioning ( table -- rev-trans-table partitions working-set )
    {
        [ reverse-transtion-table values sequence>cons ]
        [ [ transitions>> keys ] [ final-states>> keys ] bi diff 0 <subset> ]
        [ final-states>> keys 1 <subset> ]
    } cleave
    2array 
        [ sequence>cons <partitions> ]
        [ { 0 1 } swap zip >hashtable { 0 1 } sequence>cons <working-set> ]
    bi 
    ; 

: ingoing-states ( states rev-trans-table-elt -- states ) 
    '[ _ at assoc-union ] H{ } swap reduce ;

: get-next-set ( minimize-state -- set )
    ! order of quotations is important
    working-set>>
        [ sets-ids>> car>> ]
        [ sets-vector>> at ]
        [ [ cdr>> ] change-sets-ids drop ]
    tri ;

: (sub-partition) ( la sets -- new-sets )
    dup +nil+? [ nip ]
    [
        2dup
        car>> elems>> swap '[ _ key? ] partition dup empty? not [ swap ] when
        2array
        [ cdr>> (sub-partition) ] dip swons
    ] if ; recursive

: number-first-sub-partitions ( sets cnt -- first-sets )
    over +nil+? [ drop ] 
    [
        2dup { [ car>> first ] [ <subset> ] [ cdr>> ] [ 1 + ] } spread number-first-sub-partitions
        cons
    ] if ;

: number-second-sub-partitions ( sets cnt -- second-sets )
    over +nil+? [ drop ]
    [
        over car>> second empty? 
            [ 2dup { [ drop { } ] [ <subset> ] [ cdr>> ] [ ] } spread number-second-sub-partitions ] 
            [ 2dup { [ car>> second ] [ <subset> ] [ cdr>> ] [ 1 + ] } spread number-second-sub-partitions ]
        if
        cons
    ] if ;

: lzip ( list1 list2 -- list )
    2dup [ +nil+? ] bi@ or 
    [ 2drop +nil+ ]
    [
        2dup
        { [ car>> ] [ car>> 2array ] [ cdr>> ] [ cdr>> lzip ] } spread cons
    ] if ;

: number-sub-partitions ( sets -- partitions )
    [ 0 number-first-sub-partitions dup llength ] [ swap number-second-sub-partitions ] bi
    lzip ;

: update-sets-ids ( set working-set -- )
    [ id>> ] dip
    2dup sets-vector>> key?
    [ 2drop ]
    [ [ cons ] change-sets-ids drop ] if ;

: sets-ids-need-update? ( sets -- t/f )
    length 2 = ;

: filter-new-partitions ( working-set new-partitions -- working-set filtered )
    over 
    '[ 
        dup first id>> _ sets-vector>> key?
        [ [ elems>> empty? not ] filter ]
        [ first2 2dup [ elems>> length ] bi@ [ > ] [ 0 = not ] bi and [ swap ] when drop 1array ] if
    ] lmap ;

: update-working-set ( working-set new-paritions -- new-working-set )
    filter-new-partitions
    over
    '[
        _ over sets-ids-need-update? [ 2dup '[ _ update-sets-ids ] each ] when
        '[ _ [ dup id>> ] [ sets-vector>> set-at ] bi* ] each
    ] leach ; 

: update-partitions ( paritions -- new-paritions )
    [ [ first ] lmap ] [ [ second ] lmap>array [ elems>> empty? not ] filter sequence>cons ] bi
    lappend <partitions> ;

: sub-partition ( working-set paritions la -- new-working-set new-partitions )
    swap sets>> (sub-partition)
    number-sub-partitions
    [ update-working-set ] keep
    update-partitions ; 

: (my-minimize) ( rev-trans-table partitions working-set -- new-partitions )
    dup sets-ids>> +nil+? [ drop nip ]
    [
        <minimize-state> dup get-next-set 3dup
        '[
                [ tuple-slots first2 swap ]
                [ _ elems>> swap ingoing-states ]
            bi*
            sub-partition
            swap <minimize-state>
        ] foldr
        [ id>> swap working-set>> sets-vector>> delete-at ] dip
        tuple-slots first2 (my-minimize)
    ] if
    ; recursive


: my-minimize ( table -- new-table )
    prepare-state-partitioning
    (my-minimize)
    dup sets>> [ pprint "\n" print ] leach
    ; 


: reg2 ( -- reg )
    "(aaww)|(bbww)" parse-regexp construct-nfa disambiguate construct-dfa number-states ;
