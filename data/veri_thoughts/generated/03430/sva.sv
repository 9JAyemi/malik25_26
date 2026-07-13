module sky130_fd_sc_ms__xnor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

    // Y must equal the XNOR of A and B.
    check_xnor_equivalence: assert property (
        @(posedge clk) Y === (A ~^ B)
    );

    // A=0 and B=0 must drive Y high.
    check_both_low_drive_high: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // A=0 and B=1 must drive Y low.
    check_a_low_b_high_drive_low: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b1)) |-> (Y === 1'b0)
    );

    // A=1 and B=0 must drive Y low.
    check_a_high_b_low_drive_low: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b0)) |-> (Y === 1'b0)
    );

    // A=1 and B=1 must drive Y high.
    check_both_high_drive_high: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1)) |-> (Y === 1'b1)
    );

endmodule