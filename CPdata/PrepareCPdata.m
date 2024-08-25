load "pre.m";
load "csg.m";
load "csg24.dat";
filename:="CPdata.dat";
I:=Open(filename,"w");  //loads sequence L of CP data

bad:={};
for i in [1..#L] do
    if i in bad then continue i; end if;
    r:=L[i];
    level:=r`level;
    genus:=r`genus;
    index:=r`index;
    if level eq 1 then continue i; end if;

    SL2:=SL(2,Integers(level));
    GL2:=GL(2,Integers(level));   
    H1:=sub<SL2|r`matgens>;
    H1`Order:=#SL2 div index;

    for j in [(i+1)..#L] do
        if j in bad then continue j; end if;
        s:=L[j];    
        if s`level ne level or s`index ne index or s`genus ne genus then continue j; end if;
        
        H2:=sub<SL2| {SL2!B : B in s`matgens} >;
        H2`Order:=#SL2 div index;

        b,_:=IsConjugate(GL2,H1,H2);
        if b then
            bad:=bad join {j};
        end if;
    end for;

end for;

L:=[L[i]: i in [1..#L] | i notin bad];
WriteObject(I, L);

