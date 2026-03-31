module sky130_fd_sc_ms__o41a_sva (
    // DUT ports
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    // Sampling clock for SVA (DUT is purely combinational; no reset present)
    input logic CLK
);
    // Functional equivalence: X = B1 & (A1|A2|A3|A4).
    check_function_equation: assert property (
        @(posedge CLK) X == (B1 & (A1 | A2 | A3 | A4))
    );

    // If B1 is LOW, X must be LOW.
    check_B1_low_forces_X_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // If X is HIGH, B1 must be HIGH.
    check_X_high_requires_B1: assert property (
        @(posedge CLK) (X == 1'b1) |-> (B1 == 1'b1)
    );

    // If X is HIGH, at least one Ai must be HIGH.
    check_X_high_requires_some_A: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A1 | A2 | A3 | A4)
    );

    // If all Ai are LOW, X must be LOW.
    check_all_A_low_forces_X_low: assert property (
        @(posedge CLK) ((A1 | A2 | A3 | A4) == 1'b0) |-> (X == 1'b0)
    );

    // If B1 is HIGH and any Ai is HIGH, X must be HIGH.
    check_enable_and_any_A_high_sets_X: assert property (
        @(posedge CLK) (B1 & (A1 | A2 | A3 | A4)) |-> (X == 1'b1)
    );

    // A rise on X must be caused by a rise on B1 or on (A1|A2|A3|A4).
    check_output_rise_caused_by_inputs: assert property (
        @(posedge CLK) $rose(X) |-> ($rose(B1) || $rose(A1 | A2 | A3 | A4))
    );

    // A fall on X must be caused by a fall on B1 or on (A1|A2|A3|A4).
    check_output_fall_caused_by_inputs: assert property (
        @(posedge CLK) $fell(X) |-> ($fell(B1) || $fell(A1 | A2 | A3 | A4))
    );

    // If all inputs are stable, X must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(B1) && $stable(A1) && $stable(A2) && $stable(A3) && $stable(A4)) |-> $stable(X)
    );

    // If X is LOW, not both B1 and (A1|A2|A3|A4) can be HIGH.
    check_X_low_consistency: assert property (
        @(posedge CLK) (X == 1'b0) |-> !(B1 & (A1 | A2 | A3 | A4))
    );
endmodule