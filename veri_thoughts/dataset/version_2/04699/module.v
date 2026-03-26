module sky130_fd_sc_hs__o2bb2a (
    X   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    output X   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    wire A1, A2;

    assign A1 = ~A1_N;
    assign A2 = ~A2_N;

    assign X = (A1 & B1 & B2) | (A2 & (B1 | B2));

endmodule