module signal_converter_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);
    // A1 HIGH forces X HIGH.
    check_A1_high_forces_X_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b1) |-> (X == 1'b1)
    );

    // When A1 is LOW, X equals A2 & B1.
    check_when_A1_low_X_equals_A2_and_B1: assert property (
        @(posedge CLK) disable iff (!RESETn) (A1 == 1'b0) |-> (X == (A2 & B1))
    );

    // With A1 LOW and A2 LOW, X must be LOW.
    check_A1_low_A2_low_forces_X_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // With A1 LOW and B1 LOW, X must be LOW.
    check_A1_low_B1_low_forces_X_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 == 1'b0) && (B1 == 1'b0)) |-> (X == 1'b0)
    );

    // A2 & B1 both HIGH forces X HIGH.
    check_A2B1_high_forces_X_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // X HIGH implies either A1 HIGH or (A2 & B1) HIGH.
    check_X_high_implies_valid_cause: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == 1'b1) |-> ((A1 == 1'b1) || ((A2 == 1'b1) && (B1 == 1'b1)))
    );

    // X LOW implies A1 LOW and not (A2 & B1).
    check_X_low_implies_inputs_blocking: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == 1'b0) |-> ((A1 == 1'b0) && !((A2 == 1'b1) && (B1 == 1'b1)))
    );

    // Rising A1 results in X HIGH in the same cycle.
    check_A1_rise_results_in_X_high: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(A1) |-> (X == 1'b1)
    );

    // With A1 LOW and B1 HIGH, a rise on A2 results in X HIGH.
    check_A2_rise_with_A1_low_B1_high_results_X_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 == 1'b0) && (B1 == 1'b1) && $rose(A2)) |-> (X == 1'b1)
    );

    // With A1 LOW and A2 HIGH, a rise on B1 results in X HIGH.
    check_B1_rise_with_A1_low_A2_high_results_X_high: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A1 == 1'b0) && (A2 == 1'b1) && $rose(B1)) |-> (X == 1'b1)
    );
endmodule