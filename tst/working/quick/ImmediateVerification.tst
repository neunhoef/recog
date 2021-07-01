#@local G
gap> G := Group(Z(3)^0 * [ [[1,0,0],[0,1,0],[0,0,-1]], [[1,-1,-1],[0,0,1],[0,-1,0]] ]);;
gap> for i in [1..50] do
>     ri := RECOG.TestGroup(G, false, 72);
> od;
