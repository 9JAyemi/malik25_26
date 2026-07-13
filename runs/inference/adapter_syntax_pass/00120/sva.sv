module sky130_fd_sc_ms__a2111oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must match the RTL sum-of-products equation.
    check_y_matches_rtl_equation: assert property (
        @($global_clock)
        Y == ((A1 & A2 & B1 & C1 & D1) |
              (A1 & A2 & ~B1 & C1 & D1) |
              (A1 & A2 & B1 & ~C1 & D1) |
              (A1 & A2 & B1 & C1 & ~D1) |
              (~A1 & ~A2 & B1 & C1 & D1) |
              (~A1 & ~A2 & ~B1 & C1 & D1) |
              (~A1 & ~A2 & B1 & ~C1 & D1) |
              (~A1 & ~A2 & B1 & C1 & ~D1) |
              (~A1 & A2 & B1 & C1 & D1) |
              (~A1 & A2 & ~B1 & C1 & D1) |
              (~A1 & A2 & B1 & ~C1 & D1) |
              (~A1 & A2 & B1 & C1 & ~D1) |
              (A1 & ~A2 & B1 & C1 & D1) |
              (A1 & ~A2 & ~B1 & C1 & D1) |
              (A1 & ~A2 & B1 & ~C1 & D1) |
              (A1 & ~A2 & B1 & C1 & ~D1))
    );

    // Y must be high when all five data inputs are high.
    check_y_high_when_all_inputs_high: assert property (
        @($global_clock)
        (A1 & A2 & B1 & C1 & D1) |-> Y
    );

    // Y must be high when A1 and A2 are high and B1, C1, and D1 are low.
    check_y_high_when_a1_a2_high_and_others_low: assert property (
        @($global_clock)
        (A1 & A2 & ~B1 & ~C1 & ~D1) |-> Y
    );

    // Y must be high when A1 and A2 are low and B1, C1, and D1 are high.
    check_y_high_when_a1_a2_low_and_others_high: assert property (
        @($global_clock)
        (~A1 & ~A2 & B1 & C1 & D1) |-> Y
    );

    // Y must be high when A1 and A2 are low and B1 is high while C1 and D1 are low.
    check_y_high_when_a1_a2_low_b1_high_others_low: assert property (
        @($global_clock)
        (~A1 & ~A2 & B1 & ~C1 & ~D1) |-> Y
    );

    // Y must be high when A1 and A2 are low and B1 is low while C1 and D1 are high.
    check_y_high_when_a1_a2_low_b1_low_others_high: assert property (
        @($global_clock)
        (~A1 & ~A2 & ~B1 & C1 & D1) |-> Y
    );

    // Y must be high when A1 is low, A2 is high, and B1, C1, and D1 are high.
    check_y_high_when_a1_low_a2_high_others_high: assert property (
        @($global_clock)
        (~A1 & A2 & B1 & C1 & D1) |-> Y
    );

    // Y must be high when A1 is low, A2 is high, and B1 is high while C1 and D1 are low.
    check_y_high_when_a1_low_a2_high_b1_high_others_low: assert property (
        @($global_clock)
        (~A1 & A2 & B1 & ~C1 & ~D1) |-> Y
    );

    // Y must be high when A1 is low, A2 is high, and B1 is low while C1 and D1 are high.
    check_y_high_when_a1_low_a2_high_b1_low_others_high: assert property (
        @($global_clock)
        (~A1 & A2 & ~B1 & C1 & D1) |-> Y
    );

    // Y must be high when A1 is high, A2 is low, and B1, C1, and D1 are high.
    check_y_high_when_a1_high_a2_low_others_high: assert property (
        @($global_clock)
        (A1 & ~A2 & B1 & C1 & D1) |-> Y
    );

    // Y must be high when A1 is high, A2 is low, and B1 is high while C1 and D1 are low.
    check_y_high_when_a1_high_a2_low_b1_high_others_low: assert property (
        @($global_clock)
        (A1 & ~A2 & B1 & ~C1 & ~D1) |-> Y
    );

    // Y must be high when A1 is high, A2 is low, and B1 is low while C1 and D1 are high.
    check_y_high_when_a1_high_a2_low_b1_low_others_high: assert property (
        @($global_clock)
        (A1 & ~A2 & ~B1 & C1 & D1) |-> Y
    );

endmodule