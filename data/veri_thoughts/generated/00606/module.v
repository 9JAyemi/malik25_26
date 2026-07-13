module top_module (
    Y,
    A1,
    A2,
    A3,
    B1
);

    // Module ports
    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;

    assign Y = ~((A1 & A2 & A3) | B1); 

 

endmodule