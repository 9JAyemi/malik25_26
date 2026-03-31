
module my_module (
    Z   ,
    A   ,
    TE_B
);

    // Module ports
    output Z   ;
    input  A   ;
    input  TE_B;

    // Behavior
    assign Z = TE_B ? 1'b1 : A;

endmodule