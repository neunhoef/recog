gap> gens := Z(3)^0 *
>  [ [ [ 1,1,2,1,2,0,0,2,0 ],
>      [ 1,0,1,0,1,2,0,0,2 ],
>      [ 2,2,0,1,2,1,1,2,0 ],
>      [ 1,1,2,0,0,2,2,2,2 ],
>      [ 1,0,1,1,2,0,1,1,2 ],
>      [ 2,2,0,0,1,2,1,0,1 ],
>      [ 2,0,0,1,0,1,1,1,0 ],
>      [ 0,2,0,2,2,0,0,1,1 ],
>      [ 0,0,2,0,2,2,2,1,1 ] ],
>    [ [ 2,1,0,1,1,2,0,0,1 ],
>      [ 2,0,1,2,1,0,2,1,1 ],
>      [ 1,0,1,2,0,1,1,1,2 ],
>      [ 0,2,0,1,2,1,1,0,0 ],
>      [ 0,2,2,0,1,0,1,1,0 ],
>      [ 1,1,1,0,1,1,1,2,1 ],
>      [ 2,0,0,0,2,2,0,0,1 ],
>      [ 2,2,0,1,1,1,2,1,1 ],
>      [ 2,1,2,0,0,2,1,1,2 ] ] ];;
gap> for i in gens do ConvertToMatrixRep(i,3); od;
gap> g := Group(gens);;
gap> ri := RECOG.TestGroup(g,false,21998167367904);;
