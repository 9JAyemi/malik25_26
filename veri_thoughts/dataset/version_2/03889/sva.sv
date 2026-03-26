module logic_gate_assertions (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Y matches the full combinational function in the RTL.
    check_y_matches_full_function: assert property (
        @($global_clock)
        Y == ((A1 && !A2) ? B1 :
              ((!A1 && A2) ? C1 :
              ((A1 && A2) ? (B1 | C1) : 1'b0)))
    );

    // When A1 is high and A2 is low, Y follows B1.
    check_y_equals_b1_when_a1_high_a2_low: assert property (
        @($global_clock)
        (A1 && !A2) |-> (Y == B1)
    );

    // When A1 is low and A2 is high, Y follows C1.
    check_y_equals_c1_when_a1_low_a2_high: assert property (
        @($global_clock)
        (!A1 && A2) |-> (Y == C1)
    );

    // When both selects are high, Y is the OR of B1 and C1.
    check_y_equals_b1_or_c1_when_both_selects_high: assert property (
        @($global_clock)
        (A1 && A2) |-> (Y == (B1 | C1))
    );

    // When both selects are low, Y is driven low.
    check_y_low_when_both_selects_low: assert property (
        @($global_clock)
        (!A1 && !A2) |-> (Y == 1'b0)
    );

endmodule