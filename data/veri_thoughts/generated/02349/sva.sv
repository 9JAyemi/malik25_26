module sky130_fd_sc_lp__o311ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // Y implements ~(C1 & B1 & (A1 | A2 | A3)).
    check_function_equation: assert property (
        @($global_clock) Y == ~(C1 & B1 & (A1 | A2 | A3))
    );

    // If B1 is LOW, Y must be HIGH.
    check_b1_low_forces_high: assert property (
        @($global_clock) (!B1) |-> (Y == 1'b1)
    );

    // If C1 is LOW, Y must be HIGH.
    check_c1_low_forces_high: assert property (
        @($global_clock) (!C1) |-> (Y == 1'b1)
    );

    // If all A inputs are LOW, Y must be HIGH.
    check_all_A_low_forces_high: assert property (
        @($global_clock) (!A1 & !A2 & !A3) |-> (Y == 1'b1)
    );

    // If B1 and C1 are HIGH and any A is HIGH, Y must be LOW.
    check_all_high_forces_low: assert property (
        @($global_clock) (B1 & C1 & (A1 | A2 | A3)) |-> (Y == 1'b0)
    );

    // When B1 and C1 are HIGH, Y equals ~(A1 | A2 | A3).
    check_b1c1_high_defines_y: assert property (
        @($global_clock) (B1 & C1) |-> (Y == ~(A1 | A2 | A3))
    );

    // If Y is LOW, then B1 and C1 are HIGH and at least one A is HIGH.
    check_y_low_implies_inputs_high: assert property (
        @($global_clock) (Y == 1'b0) |-> (B1 & C1 & (A1 | A2 | A3))
    );

    // If Y is HIGH, then at least one of {~B1, ~C1, ~(A1|A2|A3)} is TRUE.
    check_y_high_implies_some_input_low: assert property (
        @($global_clock) (Y == 1'b1) |-> (!B1 | !C1 | ~(A1 | A2 | A3))
    );

    // With B1 and C1 HIGH, a rise of (A1|A2|A3) causes Y to fall.
    check_or_rise_causes_y_fall_when_b1c1_high: assert property (
        @($global_clock) (B1 & C1 & $rose(A1 | A2 | A3)) |-> $fell(Y)
    );

    // A fall of (A1|A2|A3) forces Y HIGH.
    check_or_fall_forces_y_high: assert property (
        @($global_clock) $fell(A1 | A2 | A3) |-> (Y == 1'b1)
    );
endmodule