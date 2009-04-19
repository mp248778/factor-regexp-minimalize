! Copyright (C) 2009 Michal Pachucki.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel sequences regexp.transition-tables fry assocs accessors arrays hashtables
regexp.dfa regexp.classes lists prettyprint vectors locals sets combinators 
deques math classes.tuple


io vocabs.loader regexp.parser regexp.nfa regexp.disambiguate regexp.minimize
tools.walker
;

IN: my-minimalize
TUPLE: Subset elems id ;
TUPLE: Partitions sets ;
TUPLE: Working-set sets-vector sets-ids ;
TUPLE: Minimize-State partitions working-set ;

:: (reverse-transtion-table) ( dict letter key' key -- )
    key key key' letter dict [ drop H{ } clone ] cache [ drop H{ } clone ] cache set-at ;

: reverse-transtion-table ( transition-table -- reversed-transition-table ) 
    transitions>> unzip [ unzip rot [ [ (reverse-transtion-table) ] 3curry ] curry 2map ] { } 2map-as concat 
    H{ } clone dup '[ _ swap call ] swapd each 
    inline ;

: prepare-state-partitioning ( table -- rev-trans-table partitions working-set )
    {
     [ reverse-transtion-table values sequence>cons ]
     [ [ transitions>> keys ] [ final-states>> keys ] bi diff 0 Subset boa ]
     [ final-states>> keys 1 Subset boa ]
    } cleave
    2array 
     [ sequence>cons Partitions boa ]
     [ { 0 1 } swap zip >hashtable { 0 1 } sequence>cons Working-set boa ]
    bi 
    inline ;

: ingoing-states ( states rev-trans-table-elt -- states ) 
    '[ _ at assoc-union ] H{ } swap reduce ;

: get-next-set ( minimize-state -- set )
    working-set>>
     [ sets-ids>> car>> ]
     [ sets-vector>> at ]
     [ [ cdr>> ] change-sets-ids drop ]
    tri ;

: (sub-partition) ( quot sets -- new-sets )
    dup +nil+? [ nip ]
    [
     2dup
     car>> elems>> swap partition dup empty? not [ swap ] when
     2array
     [ cdr>> (sub-partition) ] dip swons
    ] if inline recursive ;

: number-first-sub-partitions ( sets cnt -- first-sets )
    over +nil+? [ drop ] 
    [
        2dup { [ car>> first ] [ Subset boa ] [ cdr>> ] [ 1 + ] } spread number-first-sub-partitions
        cons
    ] if ;

: number-second-sub-partitions ( sets cnt -- second-sets )
    over +nil+? [ drop ]
    [
     over car>> second empty? 
      [ 2dup { [ drop { } ] [ Subset boa ] [ cdr>> ] [ ] } spread number-second-sub-partitions ] 
      [ 2dup { [ car>> second ] [ Subset boa ] [ cdr>> ] [ 1 + ] } spread number-second-sub-partitions ]
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

: update-working-set ( working-set new-paritions -- new-working-set )
    over 
    '[ 
      dup first id>> _ sets-vector>> key?
      [ [ elems>> empty? not ] filter ]
      [ first2 2dup [ elems>> length ] bi@ [ > ] [ 0 = not ] bi and [ swap ] when drop 1array ] if
    ] lmap
    over
    '[
      _ over sets-ids-need-update? [ 2dup '[ _ update-sets-ids ] each ] when
      '[ _ [ dup id>> ] [ sets-vector>> set-at ] bi* ] each
    ] leach
    inline ;

: update-partitions ( paritions -- new-paritions )
    [ [ first ] lmap ] [ [ second ] lmap>array [ elems>> empty? not ] filter sequence>cons ] bi
    lappend Partitions boa ;

: sub-partition ( working-set paritions la -- new-working-set new-partitions )
    '[ _ key? ] swap sets>> (sub-partition)
    number-sub-partitions
    [ update-working-set ] keep
    update-partitions
    inline ;

: (my-minimize) ( rev-trans-table partitions working-set -- new-partitions )
    dup sets-ids>> +nil+? [ drop nip ]
    [
     Minimize-State boa dup get-next-set 3dup
     '[
        [ tuple-slots first2 swap ]
        [ _ elems>> swap ingoing-states ]
       bi*
       sub-partition
       swap Minimize-State boa
     ] foldr
     [ id>> swap working-set>> sets-vector>> delete-at ] dip
     tuple-slots first2 (my-minimize)
    ] if
    inline recursive ;


: my-minimize ( table -- new-table )
    prepare-state-partitioning
    (my-minimize)
    dup sets>> [ pprint "\n" print ] leach
    inline ;


: reg2 ( -- reg )
    "(aaww)|(bbww)" parse-regexp construct-nfa disambiguate construct-dfa number-states ;
