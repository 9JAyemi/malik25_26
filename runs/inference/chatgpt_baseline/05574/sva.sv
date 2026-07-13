module sky130_fd_sc_hdll__o2bb2ai_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y matches the implemented gate-level boolean function.
    check_y_function: assert property (
        @($global_clock)
        Y == ((A1_N & A2_N) | (~B1 & ~B2))
    );

    // If either B input is high, Y reduces to A1_N & A2_N.
    check_y_reduces_when_b_high: assert property (
        @($global_clock)
        (B1 | B2) |-> (Y == (A1_N & A2_N))
    );

    // If both B inputs are low, Y must be high.
    check_b_low_forces_y_high: assert property (
        @($global_clock)
        (~B1 & ~B2) |-> (Y == 1'b1)
    );

    // If both A*_N inputs are high, Y must be high.
    check_a_high_forces_y_high: assert property (
        @($global_clock)
        (A1_N & A2_N) |-> (Y == 1'b1)
    );

    // If an A*_N input is low while a B input is high, Y must be low.
    check_blocking_case_forces_y_low: assert property (
        @($global_clock)
        ((~A1_N | ~A2_N) & (B1 | B2)) |-> (Y == 1'b0)
    );

endmodule