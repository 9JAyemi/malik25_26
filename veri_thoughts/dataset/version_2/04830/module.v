module my_module (
    input A,
    input B,
    input C,
    input D,
    input E,
    output Z
);

    // Module ports
    wire Y;
    wire AB_AND;
    wire CD_AND;
    wire AB_OR_CD_AND_E;

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Instances
    and and0 (AB_AND, A, B);
    and and1 (CD_AND, C, D);
    or or0 (AB_OR_CD_AND_E, AB_AND, CD_AND, E);
    buf buf0 (Z, AB_OR_CD_AND_E);

endmodule