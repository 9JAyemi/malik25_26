
module sky130_fd_sc_hs__a221o (
    input  A1  ,
    input  A2  ,
    input  B1  ,
    input  B2  ,
    input  C1  ,
    output X   
);

    wire X1;

    assign X1 = (A1 & A2) | (B1 & B2);
    assign X = (A1) ? B1 : C1;

endmodule
