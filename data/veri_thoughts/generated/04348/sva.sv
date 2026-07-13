module sky130_fd_sc_hd__xor2_sva (
    input logic X,
    input logic A,
    input logic B
);

    // RTL has no explicit clock or reset; logic is purely combinational.

    // X must always equal A XOR B.
    check_x_matches_xor: assert property (
        @($global_clock) (X === (A ^ B))
    );

    // 00 must produce 0.
    check_x_low_when_a0_b0: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0)) |-> (X === 1'b0)
    );

    // 01 must produce 1.
    check_x_high_when_a0_b1: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b1)) |-> (X === 1'b1)
    );

    // 10 must produce 1.
    check_x_high_when_a1_b0: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b0)) |-> (X === 1'b1)
    );

    // 11 must produce 0.
    check_x_low_when_a1_b1: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1)) |-> (X === 1'b0)
    );

endmodule