module AND4D2_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);
    // Z equals the logical AND of A, B, C, and D.
    check_z_equals_and4: assert property (
        @(posedge CLK) Z == (A & B & C & D)
    );

    // When all inputs are HIGH, Z must be HIGH.
    check_all_high_implies_z_high: assert property (
        @(posedge CLK) (A && B && C && D) |-> Z
    );

    // If any input is LOW, Z must be LOW.
    check_any_low_implies_z_low: assert property (
        @(posedge CLK) (!A || !B || !C || !D) |-> !Z
    );

    // Z can only rise when all inputs are HIGH.
    check_z_rise_requires_all_high: assert property (
        @(posedge CLK) $rose(Z) |-> (A && B && C && D)
    );

    // Z can only fall when at least one input is LOW.
    check_z_fall_requires_any_low: assert property (
        @(posedge CLK) $fell(Z) |-> (!A || !B || !C || !D)
    );

    // If inputs are stable across a cycle, Z must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D}) |-> $stable(Z)
    );
endmodule