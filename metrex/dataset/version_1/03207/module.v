
module my_module (
    X   ,
    A1  ,
    A2  ,
    B1  ,
    C1  ,
    VPWR,
    VGND
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  C1  ;
    input  VPWR;
    input  VGND;

    wire not_A1, not_A2, not_B1, not_C1, A1_and_not_B1, A2_and_not_C1;

    // Invert inputs
    not (not_A1, A1);
    not (not_A2, A2);
    not (not_B1, B1);
    not (not_C1, C1);

    // Calculate A1 AND NOT B1
    and (A1_and_not_B1, A1, not_B1);

    // Calculate A2 AND NOT C1
    and (A2_and_not_C1, A2, not_C1);

    // Calculate output
    or (X, A1_and_not_B1, A2_and_not_C1);

endmodule