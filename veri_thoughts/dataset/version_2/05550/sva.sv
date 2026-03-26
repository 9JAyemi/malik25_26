module sky130_fd_sc_hvl__xnor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

    // Y must equal the XNOR of A and B.
    check_xnor_function: assert property (
        @(posedge clk) Y == (A ~^ B)
    );

    // Matching inputs must drive Y high.
    check_equal_inputs_high: assert property (
        @(posedge clk) (A == B) |-> (Y == 1'b1)
    );

    // Different inputs must drive Y low.
    check_different_inputs_low: assert property (
        @(posedge clk) (A != B) |-> (Y == 1'b0)
    );

endmodule