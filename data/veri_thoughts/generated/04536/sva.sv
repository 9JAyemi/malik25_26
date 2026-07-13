module my_logic_gate_assertions (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y matches the gate-level equation in the RTL.
    check_y_matches_gate_equation: assert property (
        @($global_clock)
        Y == ((A1 & A2 & B1 & C1 & D1) | (B1 & C1 & D1))
    );

    // Y can only be high when B1, C1, and D1 are all high.
    check_y_high_requires_b1_c1_d1: assert property (
        @($global_clock)
        Y |-> (B1 & C1 & D1)
    );

    // B1, C1, and D1 high are sufficient to drive Y high.
    check_b1_c1_d1_high_drives_y: assert property (
        @($global_clock)
        (B1 & C1 & D1) |-> Y
    );

    // If B1, C1, and D1 are not all high, Y must be low.
    check_missing_b1_c1_d1_forces_y_low: assert property (
        @($global_clock)
        !(B1 & C1 & D1) |-> !Y
    );

endmodule