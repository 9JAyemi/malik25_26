module or3_2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must equal the OR of A, B, and C.
    check_x_matches_or_of_inputs: assert property (
        @($global_clock) X == (A | B | C)
    );

    // X must be low when all three inputs are low.
    check_x_low_when_all_inputs_low: assert property (
        @($global_clock) (!A && !B && !C) |-> !X
    );

    // X must be high when A is high.
    check_x_high_when_a_high: assert property (
        @($global_clock) A |-> X
    );

    // X must be high when B is high.
    check_x_high_when_b_high: assert property (
        @($global_clock) B |-> X
    );

    // X must be high when C is high.
    check_x_high_when_c_high: assert property (
        @($global_clock) C |-> X
    );

    // X must be low when only A is high.
    check_x_low_when_only_a_high: assert property (
        @($global_clock) (A && !B && !C) |-> !X
    );

    // X must be low when only B is high.
    check_x_low_when_only_b_high: assert property (
        @($global_clock) (!A && B && !C) |-> !X
    );

    // X must be low when only C is high.
    check_x_low_when_only_c_high: assert property (
        @($global_clock) (!A && !B && C) |-> !X
    );

    // X must be high when A and B are high.
    check_x_high_when_a_and_b_high: assert property (
        @($global_clock) (A && B) |-> X
    );

    // X must be high when A and C are high.
    check_x_high_when_a_and_c_high: assert property (
        @($global_clock) (A && C) |-> X
    );

    // X must be high when B and C are high.
    check_x_high_when_b_and_c_high: assert property (
        @($global_clock) (B && C) |-> X
    );

endmodule