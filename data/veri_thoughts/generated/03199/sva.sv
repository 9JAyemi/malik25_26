module digital_circuit_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X matches the combinational function implemented in the RTL.
    check_x_function: assert property (
        @($global_clock)
        X == ((A1 & !A2) |
              (A1 & A2 & !A3 & (B1 ^ B2)))
    );

    // A low A1 always forces X low.
    check_a1_low_forces_x_low: assert property (
        @($global_clock)
        !A1 |-> !X
    );

    // A1 high with A2 low always drives X high.
    check_a1_high_a2_low_drives_x_high: assert property (
        @($global_clock)
        (A1 & !A2) |-> X
    );

    // A1 and A2 high with A3 high always drives X low.
    check_a1_a2_high_a3_high_drives_x_low: assert property (
        @($global_clock)
        (A1 & A2 & A3) |-> !X
    );

    // With A1/A2 high and A3 low, mismatched B inputs drive X high.
    check_b_mismatch_drives_x_high: assert property (
        @($global_clock)
        (A1 & A2 & !A3 & (B1 ^ B2)) |-> X
    );

    // With A1/A2 high and A3 low, matched B inputs drive X low.
    check_b_match_drives_x_low: assert property (
        @($global_clock)
        (A1 & A2 & !A3 & !(B1 ^ B2)) |-> !X
    );

    // X stays stable when all logic inputs stay stable.
    check_x_stable_when_logic_inputs_stable: assert property (
        @($global_clock) disable iff ($initstate)
        ($stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(B2)) |-> $stable(X)
    );

endmodule