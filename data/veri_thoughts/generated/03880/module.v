module interface_module (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    B2 
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    wire Y1;

    o22ai base (
        .Y(Y1),
        .A1(A1),
        .A2(A2),
        .B1(B1),
        .B2(B2)
    );

    assign Y = Y1;

endmodule

module o22ai (
    output Y,
    input A1,
    input A2,
    input B1,
    input B2,
    input VPWR, // Typically not used in logical simulation
    input VGND  // Typically not used in logical simulation
);

    // Implement the OR-AND-Invert logic
    assign Y = ~((A1 & A2) | (B1 & B2));

endmodule
