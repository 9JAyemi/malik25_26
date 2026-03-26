module sky130_fd_sc_hdll__and2_sva (
    input logic X,
    input logic A,
    input logic B
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // X must always equal the AND of A and B.
    check_and_function: assert property (
        @($global_clock) X === (A & B)
    );

    // A low forces X low.
    check_a_low_forces_x_low: assert property (
        @($global_clock) (A === 1'b0) |-> (X === 1'b0)
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @($global_clock) (B === 1'b0) |-> (X === 1'b0)
    );

    // Both inputs high force X high.
    check_both_high_force_x_high: assert property (
        @($global_clock) ((A === 1'b1) && (B === 1'b1)) |-> (X === 1'b1)
    );

    // X high requires both inputs high.
    check_x_high_requires_both_high: assert property (
        @($global_clock) (X === 1'b1) |-> ((A === 1'b1) && (B === 1'b1))
    );

endmodule