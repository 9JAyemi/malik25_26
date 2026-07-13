module sky130_fd_sc_hd__o2bb2a (
    input  A1_N,
    input  A2_N,
    input  B1  ,
    input  B2  ,
    output X
);

    // Implement the logic for the module
    assign X = (A1_N == 1) && (A2_N == 0) && (B1 == 1) && (B2 == 0);

endmodule