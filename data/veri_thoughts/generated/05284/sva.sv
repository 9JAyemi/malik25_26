module sky130_fd_sc_lp__and2_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must always equal A AND B.
    check_and_function: assert property (
        @($global_clock) (X == (A & B))
    );

    // Both high inputs must drive X high.
    check_both_high_drive_high: assert property (
        @($global_clock) ((A == 1'b1) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // A low input must force X low.
    check_a_low_forces_low: assert property (
        @($global_clock) (A == 1'b0) |-> (X == 1'b0)
    );

    // B low input must force X low.
    check_b_low_forces_low: assert property (
        @($global_clock) (B == 1'b0) |-> (X == 1'b0)
    );

    // A high X requires both inputs high.
    check_output_high_requires_both_high: assert property (
        @($global_clock) (X == 1'b1) |-> ((A == 1'b1) && (B == 1'b1))
    );

    // A low X requires at least one input low.
    check_output_low_requires_low_input: assert property (
        @($global_clock) (X == 1'b0) |-> ((A == 1'b0) || (B == 1'b0))
    );

endmodule