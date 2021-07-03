#@local i, ri, G1, G2
gap> G1 := Group(Z(3)^0 * [ [[1,0,0],[0,1,0],[0,0,-1]], [[1,-1,-1],[0,0,1],[0,-1,0]] ]);;
gap> for i in [1..50] do
>     ri := RECOG.TestGroup(G1, false, 72);
> od;
gap> for i in [1..50] do
>     ri := RECOG.TestGroup(GL(9,5), false, Size(GL(9,5)));
> od;
