module sky130_fd_sc_ls__o311a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // No clock/reset in DUT; combinational logic sampled on $global_clock.
    // Function: X = (A1 || A2 || A3) && B1 && C1.

    // X equals the implemented Boolean function.
    check_functional_equivalence: assert property (
        @(posedge $global_clock) X == ((A1 || A2 || A3) && B1 && C1)
    );

    // If B1 is LOW, X must be LOW.
    check_B1_gates_low: assert property (
        @(posedge $global_clock) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If C1 is LOW, X must be LOW.
    check_C1_gates_low: assert property (
        @(posedge $global_clock) (C1 == 1'b0) |-> (X == 1'b0)
    );

    // If all A inputs are LOW, X must be LOW.
    check_all_A_low_forces_low: assert property (
        @(posedge $global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b0)
    );

    // If any A is HIGH and both B1 and C1 are HIGH, X must be HIGH.
    check_high_condition_implies_high: assert property (
        @(posedge $global_clock) ((A1 || A2 || A3) && B1 && C1) |-> (X == 1'b1)
    );

    // If X is HIGH, then both B1 and C1 are HIGH and at least one A is HIGH.
    check_high_output_implies_inputs: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> (B1 == 1'b1) && (C1 == 1'b1) && (A1 || A2 || A3)
    );

    // With B1 and C1 HIGH, X equals OR of A inputs.
    check_B1C1_high_reduces_to_ORA: assert property (
        @(posedge $global_clock) (B1 && C1) |-> (X == (A1 || A2 || A3))
    );

    // With any A HIGH, X equals AND of B1 and C1.
    check_anyA_high_reduces_to_ANDBC: assert property (
        @(posedge $global_clock) (A1 || A2 || A3) |-> (X == (B1 && C1))
    );

    // A rise on X requires B1, C1, and at least one A to be HIGH that cycle.
    check_rise_requires_enables_and_anyA: assert property (
        @(posedge $global_clock) $rose(X) |-> (B1 && C1 && (A1 || A2 || A3))
    );

    // If all inputs hold their values, X must hold its value.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge $global_clock) $stable({A1,A2,A3,B1,C1}) |-> $stable(X)
    );

    // A fall on X implies at least one input condition now blocks it.
    check_fall_implies_blocking_input: assert property (
        @(posedge $global_clock) $fell(X) |-> (!B1 || !C1 || !(A1 || A2 || A3))
    );

endmodule