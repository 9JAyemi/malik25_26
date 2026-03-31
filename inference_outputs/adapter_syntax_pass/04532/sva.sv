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

    // X matches the RTL combinational equation.
    check_x_matches_rtl_equation: assert property (
        @($global_clock)
        X == ((~(A1 & A2)) & (A1 ^ B1)) | ((~B1) & A1)
    );

    // When B1 is low, X reduces to A1.
    check_b1_low_reduces_to_a1: assert property (
        @($global_clock)
        (B1 == 1'b0) |-> (X == A1)
    );

    // When B1 is high, X reduces to the inverse of A1 & A2.
    check_b1_high_reduces_to_not_a1_and_a2: assert property (
        @($global_clock)
        (B1 == 1'b1) |-> (X == (~(A1 & A2)))
    );

    // When A1 is low, X must be low.
    check_a1_low_forces_x_low: assert property (
        @($global_clock)
        (A1 == 1'b0) |-> (X == 1'b0)
    );

    // When A1 and A2 are both high, X must be low.
    check_a1_a2_high_force_x_low: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b0)
    );

    // When A1 and B1 are both high, X must be low.
    check_a1_b1_high_force_x_low: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b0)
    );

    // When A1 is high and A2 is low, X must be high.
    check_a1_high_a2_low_sets_x_high: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (A2 == 1'b0)) |-> (X == 1'b1)
    );

    // When A1 is high and B1 is low, X must be high.
    check_a1_high_b1_low_sets_x_high: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (B1 == 1'b0)) |-> (X == 1'b1)
    );

endmodule