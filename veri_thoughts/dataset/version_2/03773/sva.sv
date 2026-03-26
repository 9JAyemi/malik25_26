module sky130_fd_sc_ls__xnor2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Y implements the XNOR of A and B.
    check_xnor_equivalence: assert property (
        @(posedge clk) (Y == ~(A ^ B))
    );

    // Equal inputs drive Y high.
    check_equal_inputs_drive_high: assert property (
        @(posedge clk) (A == B) |-> (Y == 1'b1)
    );

    // Different inputs drive Y low.
    check_unequal_inputs_drive_low: assert property (
        @(posedge clk) (A != B) |-> (Y == 1'b0)
    );

    // With B low, Y is the inverse of A.
    check_b_low_inverts_a: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == ~A)
    );

    // With B high, Y matches A.
    check_b_high_matches_a: assert property (
        @(posedge clk) (B == 1'b1) |-> (Y == A)
    );

endmodule