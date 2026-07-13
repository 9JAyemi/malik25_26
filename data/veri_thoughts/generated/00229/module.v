module and4_nor (
    Y  ,
    A  ,
    B  ,
    C  ,
    D  
);

    // Module ports
    output Y  ;
    input  A  ;
    input  B  ;
    input  C  ;
    input  D  ;

    // Local signals
    wire not_A;
    wire not_B;
    wire not_C;
    wire not_D;
    wire nor0_out;
    wire nor1_out;
    wire nor2_out;
    wire buf0_out;

    // Invert inputs
    not not_A (not_A, A);
    not not_B (not_B, B);
    not not_C (not_C, C);
    not not_D (not_D, D);

    // NOR gates
    nor nor0 (nor0_out, not_A, not_B);
    nor nor1 (nor1_out, nor0_out, not_C);
    nor nor2 (Y, nor1_out, not_D);

    // Buffer
    buf buf0 (buf0_out, Y);

endmodule