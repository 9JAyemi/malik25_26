module sky130_fd_sc_lp__nand2b_sva (
    input logic Y,
    input logic A_N,
    input logic B
);

    // Combinational DUT with no RTL clock or reset; sample on $global_clock.

    // Y must implement A_N OR the inversion of B.
    check_functional_equivalence: assert property (
        @($global_clock) Y == (A_N | ~B)
    );

    // A low B forces the inverted B term high, so Y must be high.
    check_b_low_forces_y_high: assert property (
        @($global_clock) (B == 1'b0) |-> (Y == 1'b1)
    );

    // A high A_N directly forces the OR output high.
    check_a_n_high_forces_y_high: assert property (
        @($global_clock) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // A low Y can only occur when A_N is low and B is high.
    check_y_low_implies_input_case: assert property (
        @($global_clock) (Y == 1'b0) |-> ((A_N == 1'b0) && (B == 1'b1))
    );

    // A_N low with B high must drive the output low.
    check_input_case_forces_y_low: assert property (
        @($global_clock) ((A_N == 1'b0) && (B == 1'b1)) |-> (Y == 1'b0)
    );

endmodule