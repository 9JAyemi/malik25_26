module sky130_fd_sc_lp__udp_mux_2to1_N (
    //# {{data|Data Signals}}
    input  A0,
    input  A1,
    output Y ,

    //# {{control|Control Signals}}
    input  S
);
    wire notS;
    assign notS = ~S;
    assign Y = (notS & A0) | (S & A1);
endmodule