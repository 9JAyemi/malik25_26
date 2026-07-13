module digital_circuit_assertions (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the implemented inverter/AND/NOR/buffer logic.
    check_output_equation: assert property (
        @($global_clock) Y == ~(~B1_N | (A1 & A2))
    );

    // A low B1_N input forces the NOR output low.
    check_b1n_low_forces_y_low: assert property (
        @($global_clock) !B1_N |-> !Y
    );

    // Both A inputs high force the AND term high and Y low.
    check_a_inputs_high_force_y_low: assert property (
        @($global_clock) (A1 && A2) |-> !Y
    );

    // With B1_N high and A1 low, the AND term is low and Y is high.
    check_b1n_high_a1_low_gives_y_high: assert property (
        @($global_clock) (B1_N && !A1) |-> Y
    );

    // With B1_N high and A2 low, the AND term is low and Y is high.
    check_b1n_high_a2_low_gives_y_high: assert property (
        @($global_clock) (B1_N && !A2) |-> Y
    );

    // If B1_N is high and Y is low, both A inputs must be high.
    check_b1n_high_y_low_requires_a_inputs_high: assert property (
        @($global_clock) (B1_N && !Y) |-> (A1 && A2)
    );

endmodule