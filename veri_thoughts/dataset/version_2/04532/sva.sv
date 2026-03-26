module sky130_fd_sc_ms__a21o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // No RTL clock or reset; sample this combinational cell on the formal global clock.
    // X depends on A1, A2, and B1; the power pins are not used in the logic.

    // X matches the exact combinational expression in the RTL.
    check_x_matches_rtl_expr: assert property (
        @($global_clock)
        X == (((~(A1 & A2)) & (A1 ^ B1)) | ((~B1) & A1))
    );

    // X simplifies to A1 XOR B1 for all input combinations.
    check_x_is_xor_of_a1_b1: assert property (
        @($global_clock)
        X == (A1 ^ B1)
    );

    // When A1 is low, X follows B1.
    check_x_follows_b1_when_a1_low: assert property (
        @($global_clock)
        (!A1) |-> (X == B1)
    );

    // When A1 is high, X is the inverse of B1.
    check_x_inverts_b1_when_a1_high: assert property (
        @($global_clock)
        A1 |-> (X == (!B1))
    );

    // When B1 is low, X follows A1.
    check_x_follows_a1_when_b1_low: assert property (
        @($global_clock)
        (!B1) |-> (X == A1)
    );

    // When B1 is high, X is the inverse of A1.
    check_x_inverts_a1_when_b1_high: assert property (
        @($global_clock)
        B1 |-> (X == (!A1))
    );

    // Equal A1 and B1 drive X low.
    check_x_low_when_inputs_equal: assert property (
        @($global_clock)
        (A1 == B1) |-> (X == 1'b0)
    );

    // Different A1 and B1 drive X high.
    check_x_high_when_inputs_differ: assert property (
        @($global_clock)
        (A1 != B1) |-> (X == 1'b1)
    );

endmodule