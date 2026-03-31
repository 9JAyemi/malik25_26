module my_module (
    Y ,
    A1,
    A2,
    B1
);

    // Module ports
    output Y ;
    input  A1;
    input  A2;
    input  B1;

    // Local signals
    wire and0_out  ;
    wire and1_out  ;
    wire and2_out  ;
    wire nor0_out_Y;

    //  Name  Output      Other arguments
    and and0 (and0_out  , A1, A2         );
    and and1 (and1_out  , and0_out, B1   );
    and and2 (and2_out  , A1, B1         );
    nor nor0 (nor0_out_Y, and1_out, and2_out);
    buf buf0 (Y         , nor0_out_Y     );

endmodule