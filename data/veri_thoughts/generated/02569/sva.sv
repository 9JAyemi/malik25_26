module and_gate_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y must equal the bitwise AND of all inputs.
    check_y_is_and_of_all: assert property (
        @(posedge $global_clock) Y == (A1 & A2 & B1 & C1 & D1)
    );

    // If Y is HIGH, then all inputs must be HIGH in the same cycle.
    check_y_high_requires_all_high: assert property (
        @(posedge $global_clock) Y |-> (A1 & A2 & B1 & C1 & D1)
    );

    // If all inputs are HIGH, then Y must be HIGH in the same cycle.
    check_all_high_implies_y_high: assert property (
        @(posedge $global_clock) (A1 & A2 & B1 & C1 & D1) |-> Y
    );

    // A1 LOW forces Y LOW in the same cycle.
    check_a1_low_forces_y_low: assert property (
        @(posedge $global_clock) (!A1) |-> (!Y)
    );

    // A2 LOW forces Y LOW in the same cycle.
    check_a2_low_forces_y_low: assert property (
        @(posedge $global_clock) (!A2) |-> (!Y)
    );

    // B1 LOW forces Y LOW in the same cycle.
    check_b1_low_forces_y_low: assert property (
        @(posedge $global_clock) (!B1) |-> (!Y)
    );

    // C1 LOW forces Y LOW in the same cycle.
    check_c1_low_forces_y_low: assert property (
        @(posedge $global_clock) (!C1) |-> (!Y)
    );

    // D1 LOW forces Y LOW in the same cycle.
    check_d1_low_forces_y_low: assert property (
        @(posedge $global_clock) (!D1) |-> (!Y)
    );

endmodule