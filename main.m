load "EarlierCode/GL2GroupTheory.m";
AttachSpec("EarlierCode/magma.spec");

/*  Load precomputed data containing all agreeable subgroups 
    of GL(2,Zhat) of genus at most 1.   It also contains some
    intermediate groups that will be useful for morphisms later.
*/    

I:=Open("Data/agreeable_groups_genus_0_and_1.dat", "r");
Families:=AssociativeArray();
repeat
	b,y:=ReadObjectCheck(I);
	if b then
		Families[y`label]:=y;
	end if;
until not b;


/*  
    The following code computes a sequence "bound" which gives
    all the upper bounds of Theorem 1.2 except the last one. 
*/    

bound:=[0,0,0,0,0];
for r in Families do
    if r`is_agreeable eq false then continue r; end if;
    assert r`genus le 1;

    /*  For the agreeable group G described by the record r,
        we have a field K_G as in the paper.  The set D below
        is the set of squarefree integers, besides 1, whose
        squareroot lies in K_G
    */
    D:={&*S: S in Subsets(Set(r`det_field)) | #S ne 0};

    bound[1]:=Maximum(bound[1],r`commutator_index);

    if {-1,2,3,5} subset D eq false then
        bound[2]:=Maximum(bound[2],r`commutator_index);
    end if;

    if &or{ 1 mod d eq 0: d in D} eq false then
        bound[3]:=Maximum(bound[3],r`commutator_index);
    end if;

    if &or{ (2*3) mod d eq 0: d in D} eq false then
        bound[4]:=Maximum(bound[4],r`commutator_index);
    end if;

    if &or{ (2*3*5*7*11) mod d eq 0: d in D} eq false then
        bound[5]:=Maximum(bound[5],r`commutator_index);
    end if;

end for;

bound;

/*  The following code produces the data of Table 1 in the paper */

{* [r`genus,r`det_index] : r in Families | r`is_agreeable *};
