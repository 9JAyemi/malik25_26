module verilog_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // No RTL clock or reset is present; sample this combinational logic on $global_clock.

    // Y must match the exact RTL sum-of-products expression.
    check_y_matches_rtl_equation: assert property (
        @($global_clock)
        Y == ((A1 & A2) | (~A1 & ~A2 & B1) | (A1 & ~A2 & ~B1) | (~A1 & A2 & ~B1))
    );

    // When B1 is low, Y reduces to A1 OR A2.
    check_b1_low_reduces_to_or: assert property (
        @($global_clock)
        (!B1) |-> (Y == (A1 | A2))
    );

    // When B1 is high, Y reduces to A1 XNOR A2.
    check_b1_high_reduces_to_xnor: assert property (
        @($global_clock)
        B1 |-> (Y == !(A1 ^ A2))
    );

    // When both A inputs are low, Y follows B1.
    check_a_inputs_low_follow_b1: assert property (
        @($global_clock)
        (!A1 && !A2) |-> (Y == B1)
    );

    // When the A inputs differ, Y is the inverse of B1.
    check_a_inputs_differ_invert_b1: assert property (
        @($global_clock)
        (A1 ^ A2) |-> (Y == !B1)
    );

    // When both A inputs are high, Y must be high.
    check_a_inputs_high_force_y_high: assert property (
        @($global_clock)
        (A1 && A2) |-> Y
    );

endmodule