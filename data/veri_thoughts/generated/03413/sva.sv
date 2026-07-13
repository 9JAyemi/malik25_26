module sky130_fd_sc_hs__a22oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND
);

    // No RTL clock or reset is present; sample this combinational logic on $global_clock.

    // Y must match the implemented sum-of-products equation.
    check_boolean_equation: assert property (
        @($global_clock)
        Y == ((~A1 & ~A2 & B1) | (~A1 & A2 & B2) | (A1 & ~A2 & B2) | (A1 & A2 & ~B1))
    );

    // When both A inputs are low, Y follows B1.
    check_follow_b1_when_a1a2_low: assert property (
        @($global_clock) (!A1 && !A2) |-> (Y == B1)
    );

    // When A1 is low and A2 is high, Y follows B2.
    check_follow_b2_when_a1_low_a2_high: assert property (
        @($global_clock) (!A1 && A2) |-> (Y == B2)
    );

    // When A1 is high and A2 is low, Y follows B2.
    check_follow_b2_when_a1_high_a2_low: assert property (
        @($global_clock) (A1 && !A2) |-> (Y == B2)
    );

    // When both A inputs are high, Y is the inverse of B1.
    check_invert_b1_when_a1a2_high: assert property (
        @($global_clock) (A1 && A2) |-> (Y == ~B1)
    );

endmodule