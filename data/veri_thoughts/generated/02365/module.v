
module sky130_fd_sc_lp__a22oi_1 (
    input  A1,
    input  A2,
    input  B1,
    input  B2,
    output Y
);

    assign Y = (A1 & A2) | (B1 & B2);

endmodule